//! Code related to structured objects.  See [`ObjGlyph`].
//!
//! [`ObjGlyph`]s differ from [`MapGlyph`]s in that
//!
//! 1. They contain additional type information, such as a type name or hash.
//! 2. All keys are field names and encoded as byte strings containing UTF-8,
//!    with a maximum length of 255 bytes.
//! 3. All key/value pairs are stored in byte string order.
use crate::{
  crypto::GlyphHash,
  glyph_close, glyph_read,
  util::SmallStrings,
  zerocopy::{round_to_word, ZeroCopy, U16, U32, U64},
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphOffset, GlyphType, ParsedGlyph,
  ToGlyph,
};
use alloc::collections::BTreeMap;
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
  str::from_utf8,
};

/// A header for object glyphs.
#[derive(Copy, Clone)]
#[repr(packed)]
pub(crate) struct ObjGlyphHeader {
  /// The object glyph format version--currently must be experimental/zero.
  version:    u8,
  /// See [`ObjGlyphHeaderFlags`]
  flags:      u8,
  /// The number of fields in the object.
  num_fields: U16,
  reserved:   U32,
}

/// SAFETY: All components are zero copy
unsafe impl ZeroCopy for ObjGlyphHeader {}

impl ObjGlyphHeader {
  /// The fields in the glyph are ordered by field name.
  const FIELDS_ORDERED: u8 = 0b0010_0000;
  /// Each offset begins with a UTF-8 string naming the field.
  const FIELD_NAMES: u8 = 0b0001_0000;
  /// The glyph contains a hash of a glyph describing its format.
  const TYPE_HASH: u8 = 0b0000_0001;
  /// The glyph contains a UTF-8 string naming the type.
  const TYPE_NAME: u8 = 0b0000_0010;
  /// The glyph contains a U64 identifying a variant of the type.
  const VARIANT_ID: u8 = 0b0000_1000;
  /// The glyph contains a UTF-8 string naming a variant of the type.
  const VARIANT_NAME: u8 = 0b0000_0100;

  /// Creates a new object glyph header.
  ///
  /// Fields:
  /// - `num_fields` is how many fields will be present in the object.  Note
  ///   that the maximum number of fields is [`u16::MAX`], and any larger
  ///   number will result in this function returning `Err(GlyphErr::Overflow)`.
  /// - `type_name` indicates whether a type name for this object will be
  ///   specified in the glyph.
  /// - `field_names` indicates whether this object glyph will store the names
  ///   of each field in the object itself.
  /// - `type_hash` indicates whether the type of this object glyph is described
  ///   by a [`GlyphHash`].
  pub fn new(
    num_fields: usize,
    type_hash: bool,
    type_name: bool,
    variant_id: bool,
    variant_name: bool,
    field_names: bool,
    fields_ordered: bool,
  ) -> Result<Self, GlyphErr> {
    let mut flags = 0u8;
    if type_hash {
      flags |= Self::TYPE_HASH
    }
    if type_name {
      flags |= Self::TYPE_NAME;
    }
    if variant_name {
      flags |= Self::VARIANT_NAME;
    }
    if variant_id {
      flags |= Self::VARIANT_ID;
    }
    if field_names {
      flags |= Self::FIELD_NAMES;
    }
    if fields_ordered {
      flags |= Self::FIELDS_ORDERED;
    }

    let num_fields: u16 = num_fields
      .try_into()
      .map_err(|_err| GlyphErr::ObjGlyphNumFieldsOverflow(num_fields))?;

    Ok(Self {
      version: 0,
      flags,
      num_fields: U16::from(num_fields),
      reserved: Default::default(),
    })
  }

  pub fn has_type_hash(&self) -> bool {
    (self.flags & Self::TYPE_HASH) != 0
  }

  pub fn has_type_name(&self) -> bool {
    (self.flags & Self::TYPE_NAME) != 0
  }

  pub fn has_variant_name(&self) -> bool {
    (self.flags & Self::VARIANT_NAME) != 0
  }

  pub fn has_variant_id(&self) -> bool {
    (self.flags & Self::VARIANT_ID) != 0
  }

  pub fn has_field_names(&self) -> bool {
    (self.flags & Self::FIELD_NAMES) != 0
  }

  pub fn has_fields_ordered(&self) -> bool {
    (self.flags & Self::FIELDS_ORDERED) != 0
  }

  /// The number of fields in the associated object glyph.
  pub fn num_fields(&self) -> usize {
    self.num_fields.get().into()
  }

  pub(crate) fn skip(cursor: &mut usize) -> usize {
    let content_start = *cursor;
    *cursor += size_of::<Self>();
    content_start
  }
}

impl Debug for ObjGlyphHeader {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("ObjGlyphHeader");
    df.field("flags", &self.flags);
    df.field("num_fields", &self.num_fields);
    df.field("has_type_hash", &self.has_type_hash());
    df.field("has_type_name", &self.has_type_name());
    df.field("has_variant_id", &self.has_variant_id());
    df.field("has_variant_name", &self.has_variant_name());
    df.field("has_field_names", &self.has_field_names());
    df.field("has_fields_ordered", &self.has_fields_ordered());
    df.finish()
  }
}

/*
Format:
- GlyphHeader, ObjGlyphHeader.
- if TYPE_HASH, a GlyphHash identifying the type (probably to a document glyph,
  which would allow us to get a newer ID if desired...)
- offsets table of `num_fields` * U32
- The remainder of the glyph is a data section.
- if TYPE_NAME is set, the
- TYPE_ID glyph.
- Each glyph, if FIELD_NAMES is set, followed by one byte for the field name
  length and then that many bytes for the field name.  By convention this should
  be valid UTF-8 but currently that is not enforced.
- Fields must be stored in (byte) order by field names (if present).
*/

/// An Object Glyph.
///
/// The binary format is as follows:
/// - An [`ObjGlyphHeader`].
/// - Iff the [`ObjGlyphHeaderFlags::TYPE_HASH`] bit is set, a [`GlyphHash`]
///   uniquely identifying the object's type.
/// - A table of `U32`s with length equal to [`ObjGlyphHeader::num_fields()`],
///   describing the offset of the contents of each field in the data section,
///   in 8-byte words.
/// - Iff the [`ObjGlyphHeaderFlags::TYPE_NAME`] bit is set, a short UTF-8
///   string (a u8 with its length and then the UTF-8 bytes).
/// - Zero padding to the nearest 8-byte word.
///

#[derive(Clone)]
pub struct ObjGlyph<B>
where
  B: Glyph,
{
  glyph:         B,
  header:        ObjGlyphHeader,
  type_hash:     Option<NonNull<GlyphHash>>,
  type_name:     Option<NonNull<str>>,
  variant_name:  Option<NonNull<str>>,
  variant_id:    Option<u64>,
  field_offsets: NonNull<[GlyphOffset]>,
}

impl<B> Copy for ObjGlyph<B> where B: Copy + Glyph {}

impl<B> FromGlyph<B> for ObjGlyph<B>
where
  B: Glyph,
{
  fn from_glyph(source: B) -> Result<Self, GlyphErr> {
    source.confirm_type(GlyphType::Object)?;
    let content = source.content_padded();
    let cursor = &mut 0;

    let header = ObjGlyphHeader::bbrd(content, cursor)?;
    let type_hash = if header.has_type_hash() {
      let hash = GlyphHash::bbrf(content, cursor)?;
      Some(NonNull::from(hash))
    } else {
      None
    };
    let type_name = if header.has_type_name() {
      let len = u8::bbrf(content, cursor)?;
      let name_bytes = u8::bbrfs(content, cursor, *len as usize)?;
      *cursor = round_to_word(*cursor);
      let name = from_utf8(name_bytes)?;
      Some(NonNull::from(name))
    } else {
      None
    };
    let variant_id = if header.has_variant_id() {
      Some(U64::bbrd(content, cursor)?.get())
    } else {
      None
    };
    let variant_name = if header.has_variant_name() {
      let len = u8::bbrf(content, cursor)?;
      let name_bytes = u8::bbrfs(content, cursor, *len as usize)?;
      *cursor = round_to_word(*cursor);
      let name = from_utf8(name_bytes)?;
      Some(NonNull::from(name))
    } else {
      None
    };

    let field_offsets =
      GlyphOffset::bbrfs(content, cursor, header.num_fields.get().into())?;
    let field_offsets = NonNull::from(field_offsets);

    Ok(Self {
      glyph: source,
      header,
      type_name,
      type_hash,
      variant_name,
      variant_id,
      field_offsets,
    })
  }
}

impl<B> ObjGlyph<B>
where
  B: Glyph,
{
  /// Returns a [`GlyphHash`] if the object's type is identified by a hash.
  pub fn type_hash(&self) -> Option<&GlyphHash> {
    unsafe { self.type_hash.map(|ptr| ptr.as_ref()) }
  }

  /// The name of the object's type, if present.
  pub fn type_name(&self) -> Option<&str> {
    unsafe { self.type_name.map(|p| p.as_ref()) }
  }

  /// The id of the object's variant, if present.
  pub fn variant_id(&self) -> Option<u64> {
    self.variant_id
  }

  /// The name of the object's variant, if present.
  pub fn variant_name(&self) -> Option<&str> {
    unsafe { self.variant_name.map(|p| p.as_ref()) }
  }

  /// The offsets of the fields in the glyph.
  fn offsets(&self) -> &[GlyphOffset] {
    unsafe { self.field_offsets.as_ref() }
  }

  /// Returns `true` if the object has field names.
  pub fn has_field_names(&self) -> bool {
    self.header.has_field_names()
  }

  /// Returns the number of fields in the object.
  pub fn len(&self) -> usize {
    self.header.num_fields()
  }

  /// Returns the field name and value of the `index`-th field.
  pub fn nth(
    &self,
    index: usize,
  ) -> Result<(Option<&str>, ParsedGlyph<'_>), GlyphErr> {
    let content = self.glyph.content_padded();

    let offset = self.offsets().get(index).ok_or(GlyphErr::OutOfBounds {
      index,
      length: self.offsets().len(),
    })?;
    let mut cursor = offset.cursor(0);

    let field_name = if self.header.has_field_names() {
      let len = u8::bbrf(content, &mut cursor)?;
      let bytes = u8::bbrfs(content, &mut cursor, *len as usize)?;
      cursor = round_to_word(cursor);
      let name = from_utf8(bytes)?;
      Some(name)
    } else {
      None
    };

    let field_value = glyph_read(content, &mut cursor)?;
    Ok((field_name, field_value))
  }

  /// Returns the value of the field with the provided name.
  ///
  /// This function performs a binary search by field name, and so can find
  /// a named field if present in `O=log(n)` time.
  pub fn by_name(&self, name: &str) -> Option<ParsedGlyph> {
    if !self.has_field_names() {
      None
    } else {
      if self.header.has_fields_ordered() {
        let content = self.glyph.content_padded();
        if let Ok(position) = self.offsets().binary_search_by(|offset| {
          let field_name =
            str::glyph_tiny_str_from_offset(content, *offset).unwrap_or("");
          field_name.cmp(name)
        }) {
          // Found a match, now just need some incantations to return it.
          self.nth(position).ok().map(|(_name, value)| value)
        } else {
          None // Did a binary search of the list; nothing found.
        }
      } else {
        for (field_name, field) in self.fields_iter() {
          if let Some(field_name) = field_name {
            if field_name.eq(name) {
              return Some(field);
            }
          }
        }
        None // Got to the end of list; nothing found.
      }
    }
  }

  /// Returns an iterator through fields and field names (if present).
  fn fields_iter(
    &self,
  ) -> impl Iterator<Item = (Option<&str>, ParsedGlyph)> + Clone + DoubleEndedIterator
  {
    IterFields {
      content:      self.glyph.content_padded(),
      offsets:      self.offsets(),
      named_fields: self.header.has_field_names(),
    }
  }
}

impl<'a> ObjGlyph<ParsedGlyph<'a>> {
  fn offsets_parsed(&self) -> &'a [GlyphOffset] {
    unsafe { self.field_offsets.as_ref() }
  }

  /// Returns the `index`-th field in the object.
  ///
  /// This function retrieves the field name and value at the specified `index`.
  /// If the object has field names, the returned tuple will include the field
  /// name as `Some(&str)`; otherwise, it will be `None`. The field value is
  /// returned as a [`ParsedGlyph`].
  ///
  /// # Arguments
  ///
  /// * `index` - The zero-based index of the field to retrieve.
  ///
  /// # Returns
  ///
  /// * `Ok((Option<&'a str>, ParsedGlyph<'a>))` - A tuple containing the
  ///   optional field name and the field value if the field exists at the
  ///   specified index.
  ///
  /// # Errors
  ///
  /// This function will return:
  /// * `GlyphErr::OutOfBounds` if the provided `index` is greater than or equal to the number of fields.
  /// * Any error that occurs during decoding of the field name or content.
  pub fn nth_parse(
    &self,
    index: usize,
  ) -> Result<(Option<&'a str>, ParsedGlyph<'a>), GlyphErr> {
    let content = self.glyph.content_padded_parsed();

    let offset = self.offsets().get(index).ok_or(GlyphErr::OutOfBounds {
      index,
      length: self.offsets().len(),
    })?;
    let mut cursor = offset.cursor(0);

    let field_name = if self.header.has_field_names() {
      let len = u8::bbrf(content, &mut cursor)?;
      let bytes = u8::bbrfs(content, &mut cursor, *len as usize)?;
      cursor = round_to_word(cursor);
      let name = from_utf8(bytes)?;
      Some(name)
    } else {
      None
    };

    let field_value = glyph_read(content, &mut cursor)?;
    Ok((field_name, field_value))
  }

  /// Returns an iterator through fields, parsed from the underlying buffer.
  ///
  /// This function creates an iterator that traverses all the fields in the object
  /// and yields a tuple consisting of an optional field name and the corresponding
  /// [`ParsedGlyph`] value.
  ///
  /// # Returns
  ///
  /// * `impl Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)>` - An iterator
  ///   where each item is a tuple containing:
  ///     - `Option<&'a str>`: The field name if it exists, or `None` if the
  ///       object does not have named fields.
  ///     - `ParsedGlyph<'a>`: The parsed value of the field.
  pub fn fields_iter_parse(
    &self,
  ) -> impl Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)>
       + Clone
       + DoubleEndedIterator {
    IterFields {
      content:      self.glyph.content_padded_parsed(),
      offsets:      self.offsets_parsed(),
      named_fields: self.header.has_field_names(),
    }
  }
}

impl<'a> ObjGlyph<ParsedGlyph<'a>> {
  /// Returns a [`GlyphHash`] if the object's type is identified by a hash.
  pub fn type_hash_parsed(&self) -> Option<&'a GlyphHash> {
    unsafe { self.type_hash.map(|ptr| ptr.as_ref()) }
  }

  /// Returns the object's type name, if present, parsed from the underlying
  /// buffer.
  pub fn type_name_parsed(&self) -> Option<&'a str> {
    unsafe { self.type_name.map(|p| p.as_ref()) }
  }

  /// Returns the object's variant name, if present, parsed from the underlying
  /// buffer.
  pub fn variant_name_parsed(&self) -> Option<&'a str> {
    unsafe { self.variant_name.map(|p| p.as_ref()) }
  }

  /// Returns the value of the field with the provided name, with lifetime bound
  /// by the backing buffer rather than this `ObjGlyph`.
  ///
  /// This function searches for a field by its name. If the field names are
  /// ordered, a binary search is performed for efficiency. Otherwise, an
  /// iterative search is used.
  ///
  /// # Arguments
  ///
  /// * `name` - A `&str` reference representing the name of the field to search for.
  ///
  /// # Returns
  ///
  /// * `Option<ParsedGlyph>` - If a field with the provided name exists, returns
  ///   its value wrapped in `Some`. Otherwise, returns `None`.
  pub fn by_name_parsed(&self, name: &str) -> Option<ParsedGlyph> {
    if !self.has_field_names() {
      None
    } else {
      if self.header.has_fields_ordered() {
        let content = self.glyph.content_padded_parsed();
        if let Ok(position) = self.offsets().binary_search_by(|offset| {
          let field_name =
            str::glyph_tiny_str_from_offset(content, *offset).unwrap_or("");
          field_name.cmp(name)
        }) {
          // Found a match, now just need some incantations to return it.
          self.nth(position).ok().map(|(_name, value)| value)
        } else {
          None // Did a binary search of the list; nothing found.
        }
      } else {
        for (field_name, field) in self.fields_iter() {
          if let Some(field_name) = field_name {
            if field_name.eq(name) {
              return Some(field);
            }
          }
        }
        None // Got to the end of list; nothing found.
      }
    }
  }
}

impl<T: Glyph> Debug for ObjGlyph<T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    struct TupleFields<'a, T>(T)
    where
      T: Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)> + Clone;

    impl<'a, T> Debug for TupleFields<'a, T>
    where
      T: Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)> + Clone,
    {
      fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut df = f.debug_list();
        for (_field_name, field) in self.0.clone() {
          df.entry(&field);
        }
        df.finish()
      }
    }

    struct NamedFields<'a, T>(T)
    where
      T: Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)> + Clone;

    impl<'a, T> Debug for NamedFields<'a, T>
    where
      T: Iterator<Item = (Option<&'a str>, ParsedGlyph<'a>)> + Clone,
    {
      fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut df = f.debug_map();
        for (field_name, field) in self.0.clone() {
          let field_name = field_name.unwrap_or("MISSING");
          df.entry(&field_name, &field);
        }
        df.finish()
      }
    }

    let mut df = f.debug_struct("ObjGlyph");
    if let Some(type_hash) = self.type_hash() {
      df.field("type_hash", &type_hash);
    } else {
      df.field("type_hash", &Option::<()>::None);
    }
    if let Some(type_name) = self.type_name() {
      df.field("type_name", &type_name);
    } else {
      df.field("type_name", &Option::<()>::None);
    }
    if let Some(id) = self.variant_id() {
      df.field("variant_id", &id);
    } else {
      df.field("variant_id", &Option::<()>::None);
    }
    if let Some(name) = self.variant_name() {
      df.field("variant_name", &name);
    } else {
      df.field("variant_name", &Option::<()>::None);
    }
    if self.has_field_names() {
      let nf = NamedFields(self.fields_iter());
      df.field("fields", &nf);
    } else {
      let tf = TupleFields(self.fields_iter());
      df.field("fields", &tf);
    }

    df.finish()
  }
}

/// An iterator through the fields of an [`ObjGlyph`].
#[derive(Clone, Copy)]
pub(crate) struct IterFields<'a> {
  /// The contents of the [`ObjGlyph`].
  content: &'a [u8],

  /// The offset of each field
  offsets: &'a [GlyphOffset],

  /// Whether the fields are named.
  named_fields: bool,
}

impl<'a> Iterator for IterFields<'a> {
  type Item = (Option<&'a str>, ParsedGlyph<'a>);

  fn next(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_first()?;
    self.offsets = remainder;
    let cursor = &mut offset.cursor(0);

    let field_name = if self.named_fields {
      let len = u8::bbrf(self.content, cursor).ok()?;
      let bytes = u8::bbrfs(self.content, cursor, *len as usize).ok()?;
      *cursor = round_to_word(*cursor);
      let name = from_utf8(bytes).ok()?;
      Some(name)
    } else {
      None
    };

    let field_value = glyph_read(self.content, cursor).ok()?;
    Some((field_name, field_value))
  }
}

impl<'a> DoubleEndedIterator for IterFields<'a> {
  fn next_back(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_last()?;
    self.offsets = remainder;
    let cursor = &mut offset.cursor(0);

    let field_name = if self.named_fields {
      let len = u8::bbrf(self.content, cursor).ok()?;
      let bytes = u8::bbrfs(self.content, cursor, *len as usize).ok()?;
      *cursor = round_to_word(*cursor);
      let name = from_utf8(bytes).ok()?;
      Some(name)
    } else {
      None
    };

    let field_value = glyph_read(self.content, cursor).ok()?;
    Some((field_name, field_value))
  }
}

/// Calculates the length of an [`ObjGlyph`], in bytes.
///
///
///
pub(crate) struct ObjGlyphLenCalc {
  /// Length of the type IDs, variant IDs, and field names (if present)
  labels_len: usize,
  /// The number of fields to be serialized (necessary to calculate length of
  /// offsets table.
  num_fields: usize,
  /// The total length of all field values to be serialized in the object.
  fields_len: usize,
}

impl ObjGlyphLenCalc {
  /// Starts a new [`ObjGlyph`] length calculation.
  ///
  /// Parameters:
  /// - `type_hash` Does the object include a hash referencing more information
  ///   about the type?
  /// - `type_name` If the object will have a type name, include it here.
  /// - `variant_name` If the object will have a variant name (e.g., for the
  ///   discriminant of an `enum`), include it here.
  /// - `variant_id` If the object will have a variant identifier (e.g., for the
  ///   value of an `enum`), include it here.
  pub fn new(
    type_hash: bool,
    type_name: Option<&str>,
    variant_name: Option<&str>,
    variant_id: bool,
  ) -> Result<Self, GlyphErr> {
    let mut labels_len = 0;
    if type_hash {
      labels_len += size_of::<GlyphHash>();
    }
    if let Some(type_name) = type_name {
      labels_len += type_name.glyph_tiny_str_len()?;
    }
    if let Some(variant_name) = variant_name {
      labels_len += variant_name.glyph_tiny_str_len()?;
    }
    if variant_id {
      labels_len += size_of::<U64>();
    }
    Ok(ObjGlyphLenCalc {
      labels_len,
      num_fields: 0,
      fields_len: 0,
    })
  }

  /// Adds the length necessary to include a new field.
  ///
  /// Note: Calling this function with field names only some of the time will
  ///       not produce a valid length--this property is per-_object_, not
  ///       per-field.
  pub fn add_field(
    &mut self,
    field_name: Option<&str>,
    field_len: usize,
  ) -> Result<(), GlyphErr> {
    if let Some(field_name) = field_name {
      let field_name_len = field_name.glyph_tiny_str_len()?;
      self.labels_len = self.labels_len.saturating_add(field_name_len);
    }
    self.num_fields = self.num_fields.saturating_add(1);
    self.fields_len = self.fields_len.saturating_add(field_len);
    Ok(())
  }

  pub fn finish(self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<ObjGlyphHeader>()
      + self.labels_len
      + round_to_word(size_of::<GlyphOffset>() * self.num_fields)
      + self.fields_len
  }
}

/// Serializes an [`ObjGlyph`].
///
/// Upon creation with [`new()`], internal headers, labels (where appropriate),
/// and the offsets table are written immediately.  Field names (if present)
/// and values are written with [`add_field()`], and the final headers are
/// written with [`finish()`].
///
/// Note that the number of fields and total length must be known in advance,
/// or the serialized glyph will not be valid.  The latter can be determined
/// with [`ObjGlyphLenCalc`].
pub(crate) struct ObjGlyphSerializer<'a> {
  target:         &'a mut [u8],
  glyph_start:    usize,
  content_start:  usize,
  offsets_cursor: usize,
  cursor:         &'a mut usize,
}

impl<'a> ObjGlyphSerializer<'a> {
  /// Starts serializing an [`ObjGlyph`].
  ///
  /// Internal headers, labels (where appropriate), and the offsets table are
  /// written immediately.
  pub(crate) fn new(
    type_hash: Option<&GlyphHash>,
    type_name: Option<&str>,
    variant_id: Option<u64>,
    variant_name: Option<&str>,
    field_names: bool,
    fields_ordered: bool,
    length: usize,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    //== Set up Headers and Object-Level Labels ==/
    let glyph_start = GlyphHeader::skip(cursor);
    let content_start = *cursor;
    ObjGlyphHeader::new(
      length,
      type_hash.is_some(),
      type_name.is_some(),
      variant_id.is_some(),
      variant_name.is_some(),
      field_names,
      fields_ordered,
    )?
    .bbwr(target, cursor)?;
    if let Some(type_hash) = type_hash {
      type_hash.bbwr(target, cursor)?;
    }
    if let Some(type_name) = type_name {
      type_name.glyph_tiny_str_write(target, cursor)?;
    }
    if let Some(variant_id) = variant_id {
      U64::from(variant_id).bbwr(target, cursor)?;
    }
    if let Some(variant_name) = variant_name {
      variant_name.glyph_tiny_str_write(target, cursor)?;
    }

    //== Set up offsets table ==/
    let offsets_cursor = GlyphOffset::skip(target, cursor, length, true)?;

    Ok(Self {
      target,
      glyph_start,
      content_start,
      offsets_cursor,
      cursor,
    })
  }

  pub fn add_field<T>(
    &mut self,
    field_name: Option<&str>,
    field_value: &T,
  ) -> Result<(), GlyphErr>
  where
    T: ToGlyph,
  {
    GlyphOffset::new(self.content_start, *self.cursor)?
      .bbwr(self.target, &mut self.offsets_cursor)?;
    if let Some(field_name) = field_name {
      field_name.glyph_tiny_str_write(self.target, self.cursor)?;
    }
    field_value.glyph_encode(self.target, self.cursor)
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    glyph_close(
      GlyphType::Object,
      self.target,
      self.glyph_start,
      self.cursor,
      false,
    )?;
    Ok(())
  }
}

struct ObjGlyphMapWriter<K, V> {
  type_hash:    Option<GlyphHash>,
  type_name:    Option<alloc::string::String>,
  variant_id:   Option<u64>,
  variant_name: Option<alloc::string::String>,
  data:         BTreeMap<K, V>,
}

impl<K, V> ToGlyph for ObjGlyphMapWriter<K, V>
where
  K: Ord + AsRef<str>,
  V: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut ogs = ObjGlyphSerializer::new(
      self.type_hash.as_ref(),
      self.type_name.as_deref(),
      self.variant_id,
      self.variant_name.as_deref(),
      true,
      true,
      self.data.len(),
      target,
      cursor,
    )?;
    for (key, value) in self.data.iter() {
      ogs.add_field(Some(key.as_ref()), value)?;
    }
    ogs.finish()
  }

  fn glyph_len(&self) -> usize {
    if let Ok(mut oglc) = ObjGlyphLenCalc::new(
      self.type_hash.is_some(),
      self.type_name.as_deref(),
      self.variant_name.as_deref(),
      self.variant_id.is_some(),
    ) {
      for (key, value) in self.data.iter() {
        oglc.add_field(Some(key.as_ref()), value.glyph_len()).ok();
      }
      oglc.finish()
    } else {
      0
    }
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::glyph_new;
  use std::{
    collections::BTreeMap,
    println,
    string::{String, ToString},
  };

  #[test]
  fn obj_glyph() {
    // Basic Encoding
    let fields: BTreeMap<String, i32> =
      ('a'..='z').map(|c| String::from(c)).zip(1..=26).collect();
    let ogmw = ObjGlyphMapWriter {
      type_hash:    None,
      type_name:    Some("TestType".to_string()),
      variant_id:   None,
      variant_name: None,
      data:         fields,
    };
    let encoded = glyph_new(&ogmw).unwrap();
    // dbg!(&encoded);
    let decoded = ObjGlyph::from_glyph(encoded).unwrap();
    // dbg!(&decoded);

    // Testing binary search
    for key in ogmw.data.keys() {
      let value = decoded.by_name(key.as_str());
      let decoded_value = i32::from_glyph(value.unwrap()).unwrap();
      println!("{key:?}, {decoded_value:?}");
    }

    // LATER: Expand testing, look to cover most / all paths.
  }
}
