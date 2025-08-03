//! Code related to structured objects.  See [`ObjGlyph`].
//!
//! [`ObjGlyph`]s differ from [`MapGlyph`]s in that (1) they contain additional
//! type information (e.g., type and variant names) and (2) field names are
//! labeled with an optional (`str`) name rather than with arbitrary glyphs.
//!
// TODO: Transfer this to documentation and provide a link.
// 1. They contain additional type information, such as a type name or hash.
// 2. All keys are field names and encoded as byte strings containing UTF-8,
//    with a maximum length of 255 bytes.
// 3. All key/value pairs are stored in byte string order.
use crate::{
  crypto::GlyphHash,
  dynamic::DynGlyph,
  glyph_close,
  util::SmallStrings,
  zerocopy::{round_to_word, ZeroCopy, U16, U32, U64},
  DecodeErr, EncodedGlyph, FromGlyph, Glyph, GlyphErr,
  GlyphHeader, GlyphOffset, GlyphSorting, GlyphType, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
  str::from_utf8,
};
use std::{cmp::Ordering, ops::Deref};

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

unsafe impl ZeroCopy for ObjGlyphHeader {}

// TODO: Transfer this binary format to the appropriate documentation and link.
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
// The binary format is as follows:
// - An [`ObjGlyphHeader`].
// - Iff the [`ObjGlyphHeaderFlags::TYPE_HASH`] bit is set, a [`GlyphHash`]
//   uniquely identifying the object's type.
// - A table of `U32`s with length equal to [`ObjGlyphHeader::num_fields()`],
//   describing the offset of the contents of each field in the data section,
//   in 8-byte words.
// - Iff the [`ObjGlyphHeaderFlags::TYPE_NAME`] bit is set, a short UTF-8
//   string (a u8 with its length and then the UTF-8 bytes).
// - Zero padding to the nearest 8-byte word.
//

/// A semi-structured Object Glyph.
///
/// - Object glyphs can have an object-level type name (`str`) or hash, as well
///   as a variant name (`str`) or identifier (`u64`).
/// - Each object glyph contains a list of fields with optional (`str`) names.
///
#[derive(Clone)]
pub struct ObjGlyph<B>
where
  B: Deref<Target = Glyph>,
{
  glyph:         B,
  header:        ObjGlyphHeader,
  type_hash:     Option<NonNull<GlyphHash>>,
  type_name:     Option<NonNull<str>>,
  variant_name:  Option<NonNull<str>>,
  variant_id:    Option<u64>,
  field_offsets: NonNull<[GlyphOffset]>,
}

impl<B> ObjGlyph<B>
where
  B: Deref<Target = Glyph>,
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
  pub fn nth(&self, index: usize) -> Result<(Option<&str>, &Glyph), GlyphErr> {
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

    let field_value = Glyph::read(content, &mut cursor)?;
    Ok((field_name, field_value))
  }

  /// Returns the value of the field with the provided name.
  ///
  /// This function performs a binary search by field name, and so can find
  /// a named field if present in `O=log(n)` time.
  pub fn by_name(&self, name: &str) -> Option<&Glyph> {
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
  ) -> impl Iterator<Item = (Option<&str>, &Glyph)> + Clone + DoubleEndedIterator
  {
    IterFields {
      content:      self.glyph.content_padded(),
      offsets:      self.offsets(),
      named_fields: self.header.has_field_names(),
    }
  }
}

impl<'a> ObjGlyph<&'a Glyph> {
  fn offsets_parsed(&self) -> &'a [GlyphOffset] {
    unsafe { self.field_offsets.as_ref() }
  }

  /// Returns the `index`-th field in the object.
  ///
  /// This function retrieves the field name and value at the specified `index`.
  /// If the object has field names, the returned tuple will include the field
  /// name as `Some(&str)`; otherwise, it will be `None`. The field value is
  /// returned as a `&`[`Glyph`].
  ///
  /// # Arguments
  ///
  /// * `index` - The zero-based index of the field to retrieve.
  ///
  /// # Returns
  ///
  /// * `Ok((Option<&'a str>, &'a Glyph))` - A tuple containing the
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
  ) -> Result<(Option<&'a str>, &'a Glyph), GlyphErr> {
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

    let field_value = Glyph::read(content, &mut cursor)?;
    Ok((field_name, field_value))
  }

  /// Returns an iterator through fields, parsed from the underlying buffer.
  ///
  /// This function creates an iterator that traverses all the fields in the object
  /// and yields a tuple consisting of an optional field name and the corresponding
  /// [`Glyph`] value.
  ///
  /// # Returns
  ///
  /// * `impl Iterator<Item = (Option<&'a str>, &'a Glyph)>` - An iterator
  ///   where each item is a tuple containing:
  ///     - `Option<&'a str>`: The field name if it exists, or `None` if the
  ///       object does not have named fields.
  ///     - `&'a Glyph`: The parsed value of the field.
  pub fn fields_iter_parse(
    &self,
  ) -> impl Iterator<Item = (Option<&'a str>, &'a Glyph)> + Clone + DoubleEndedIterator
  {
    IterFields {
      content:      self.glyph.content_padded(),
      offsets:      self.offsets_parsed(),
      named_fields: self.header.has_field_names(),
    }
  }

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
  pub fn by_name_parsed(&self, name: &str) -> Option<&Glyph> {
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
}

// TODO: This is dangerous given the unsafe... do we need it?
impl<B> Copy for ObjGlyph<B> where B: Copy + Deref<Target = Glyph> {}

impl<T: Deref<Target = Glyph>> Debug for ObjGlyph<T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    struct TupleFields<'a, T>(T)
    where
      T: Iterator<Item = (Option<&'a str>, &'a Glyph)> + Clone;

    impl<'a, T> Debug for TupleFields<'a, T>
    where
      T: Iterator<Item = (Option<&'a str>, &'a Glyph)> + Clone,
    {
      fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut df = f.debug_list();
        for (_field_name, field) in self.0.clone() {
          let field = DynGlyph::new(field);
          df.entry(&field);
        }
        df.finish()
      }
    }

    struct NamedFields<'a, T>(T)
    where
      T: Iterator<Item = (Option<&'a str>, &'a Glyph)> + Clone;

    impl<'a, T> Debug for NamedFields<'a, T>
    where
      T: Iterator<Item = (Option<&'a str>, &'a Glyph)> + Clone,
    {
      fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let mut df = f.debug_map();
        for (field_name, field) in self.0.clone() {
          let field_name = field_name.unwrap_or("MISSING");
          let field = DynGlyph::new(field);
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

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for ObjGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph.deref()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::TypeAndBytes => {
        self.glyph.content().cmp(&other.glyph.content())
      },
      GlyphSorting::Experimental => {
        let mut self_iter = self.fields_iter();
        let mut other_iter = other.fields_iter();

        loop {
          match (self_iter.next(), other_iter.next()) {
            (Some((a_fn, a_val)), Some((b_fn, b_val))) => {
              let ordering = a_fn.cmp(&b_fn).then_with(|| {
                let a_val = DynGlyph::new(a_val);
                let b_val = DynGlyph::new(b_val);
                a_val.glyph_ord(&b_val, sorting)
              });
              if ordering != Ordering::Equal {
                return ordering;
              }
            },
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (None, None) => return Ordering::Equal,
          }
        }
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for ObjGlyph<G> {}

impl<B> FromGlyph<B> for ObjGlyph<B>
where
  B: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: B) -> Result<Self, DecodeErr<B, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Object) {
      return Err(DecodeErr::new(source, err));
    }
    let content = source.content_padded();
    let cursor = &mut 0;

    let header = match ObjGlyphHeader::bbrd(content, cursor) {
      Ok(header) => header,
      Err(err) => return Err(DecodeErr::new(source, err.into())),
    };
    let type_hash = if header.has_type_hash() {
      let hash = match GlyphHash::bbrf(content, cursor) {
        Ok(hash) => hash,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      Some(NonNull::from(hash))
    } else {
      None
    };
    let type_name = if header.has_type_name() {
      let len = match u8::bbrf(content, cursor) {
        Ok(l) => l,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      let name_bytes = match u8::bbrfs(content, cursor, *len as usize) {
        Ok(bytes) => bytes,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      *cursor = round_to_word(*cursor);
      let name = match from_utf8(name_bytes) {
        Ok(n) => n,
        Err(e) => return Err(DecodeErr::new(source, e.into())),
      };
      Some(NonNull::from(name))
    } else {
      None
    };
    let variant_id = if header.has_variant_id() {
      let id = match U64::bbrd(content, cursor) {
        Ok(value) => value,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      Some(id.get())
    } else {
      None
    };
    let variant_name = if header.has_variant_name() {
      let len = match u8::bbrf(content, cursor) {
        Ok(l) => l,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      let name_bytes = match u8::bbrfs(content, cursor, *len as usize) {
        Ok(bytes) => bytes,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
      *cursor = round_to_word(*cursor);
      let name = match from_utf8(name_bytes) {
        Ok(n) => n,
        Err(e) => return Err(DecodeErr::new(source, e.into())),
      };
      Some(NonNull::from(name))
    } else {
      None
    };

    let field_offsets =
      match GlyphOffset::bbrfs(content, cursor, header.num_fields.get().into())
      {
        Ok(offsets) => offsets,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
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

impl<G: Deref<Target = Glyph>> Ord for ObjGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for ObjGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for ObjGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
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

    let field_value = Glyph::read(self.content, cursor).ok()?;
    Some((field_name, field_value))
  }
}

impl<'a> ExactSizeIterator for IterFields<'a> {
  fn len(&self) -> usize {
    self.offsets.len()
  }
}

impl<'a> Iterator for IterFields<'a> {
  type Item = (Option<&'a str>, &'a Glyph);

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

    let field_value = Glyph::read(self.content, cursor).ok()?;
    Some((field_name, field_value))
  }
}

#[doc(hidden)]
/// Calculates the length of an [`ObjGlyph`], in bytes.
///
/// This type allows user to calculate the length of an Object Glyph, typically
/// in advance of writing one using [`ObjGlyphSerializer`].  This is done by
/// first calling `new()` with object-level details, a series of successive
/// calls to `add_field()` for each field the object contains, and finally a
/// call to `finish()` to obtain the number of bytes necessary to encode the
/// described object.
pub struct ObjGlyphLenCalc {
  /// Length of the type IDs, variant IDs, and field names (if present).
  ///
  /// This is a consolidation of the type hash, type name, and variant name, and
  /// (presence of a) variant id as specified when the length calculator is
  /// created with a call to `new()`.
  labels_len: usize,

  /// The number of fields to be serialized (necessary to calculate length of
  /// the offset table).
  ///
  /// This will increase with successive calls to `add_field()`.
  num_fields: usize,

  /// The total length of all field values to be serialized in the object.
  fields_len: usize,

  /// Whether the object has named fields.
  ///
  /// This is necessary to give errors if the user calls `add_field()`
  /// incorrectly.
  named_fields: bool,
}

impl ObjGlyphLenCalc {
  /// Starts a new [`ObjGlyph`] length calculation.
  ///
  /// Parameters:
  /// - `type_hash`. Does the object include a hash referencing more information
  ///   about the type?
  /// - `type_name`. If the object will have a type name, include it here.
  /// - `variant_name`. If the object will have a variant name (e.g., for the
  ///   discriminant of an `enum`), include it here.
  /// - `variant_id`. If the object will have a variant identifier (e.g., for the
  ///   value of an `enum`), include it here.
  /// - `named_fields`. Whether or not the fields of the object will be named
  ///   (i.e., whether `add_field()` should expect field names or not).  This
  ///   must be consistent for all fields of the object.
  pub fn new(
    type_hash: bool,
    type_name: Option<&str>,
    variant_name: Option<&str>,
    variant_id: bool,
    named_fields: bool,
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
      named_fields,
    })
  }

  /// Tracks the length necessary to include another field.
  pub fn add_field(
    &mut self,
    field_name: Option<&str>,
    field_len: usize,
  ) -> Result<(), ObjGlyphErr> {
    if field_name.is_some() != self.named_fields {
      return Err(ObjGlyphErr::NamedFieldsInconsistency);
    }
    if let Some(field_name) = field_name {
      let field_name_len = field_name
        .glyph_tiny_str_len()
        .map_err(|_| ObjGlyphErr::FieldNameTooLong(field_name.len()))?;
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
pub struct ObjGlyphSerializer<'a> {
  target:         &'a mut [u8],
  glyph_start:    usize,
  content_start:  usize,
  offsets_cursor: usize,
  cursor:         &'a mut usize,
}

impl<'a> ObjGlyphSerializer<'a> {
  /// Starts serializing an [`ObjGlyph`].
  ///
  /// Parameters:
  ///
  /// - `type_hash`. The hash of a glyph describing this object type, if
  ///   present.
  /// - `type_name`. A human-readable name of the object type, if present.
  /// - `variant_name`. A human-readable name of the object's variant, if
  ///   applicable.
  /// - `variant_id`. A numeric identifier of the object's variant, if
  ///   applicable.
  /// - `field_names`. Whether or not fields will be named.
  /// - `fields_ordered`. Whether or not the fields provided to the
  ///   `add_field()` method will be named.  This must be consistent across the
  ///   entire object.
  /// - `num_fields`.  The number of fields in the object.
  /// - `target`. The byte buffer into which the object glyph will be written.
  /// - `cursor`. The location in the target byte buffer at which the object
  ///   glyph will be written.
  ///
  /// Errors:
  ///
  /// - If `type_name` or `variant_name` are more than 255 bytes.
  pub fn new(
    type_hash: Option<&GlyphHash>,
    type_name: Option<&str>,
    variant_name: Option<&str>,
    variant_id: Option<u64>,
    field_names: bool,
    fields_ordered: bool,
    num_fields: usize,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    //== Set up Headers and Object-Level Labels ==/
    let glyph_start = *cursor;
    *cursor += size_of::<GlyphHeader>();
    let content_start = *cursor;
    ObjGlyphHeader::new(
      num_fields,
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
    let offsets_cursor = GlyphOffset::skip(target, cursor, num_fields, true)?;

    Ok(Self {
      target,
      glyph_start,
      content_start,
      offsets_cursor,
      cursor,
    })
  }

  /// Writes an additional field.
  pub fn add_field<T>(
    &mut self,
    field_name: Option<&str>,
    field_value: &T,
  ) -> Result<(), GlyphErr>
  where
    T: ToGlyph,
  {
    GlyphOffset::new(*self.cursor - self.content_start)?
      .bbwr(self.target, &mut self.offsets_cursor)?;
    if let Some(field_name) = field_name {
      field_name.glyph_tiny_str_write(self.target, self.cursor)?;
    }
    field_value.glyph_encode(self.target, self.cursor)
  }

  /// Finishes writing the glyph.
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

/// Errors related to Object Glyphs.
#[derive(Debug, Copy, Clone)]
pub enum ObjGlyphErr {
  /// When writing an object glyph, either all or no fields must be named.
  NamedFieldsInconsistency,

  /// The maximum length of field names is 255 bytes.
  FieldNameTooLong(usize),
}

#[cfg(test)]
pub(crate) mod test {
  use super::*;
  use std::string::{String, ToString};

  pub(crate) struct TestObject {
    pub name: String,
    pub age:  u8,
  }

  impl ToGlyph for TestObject {
    fn glyph_encode(
      &self,
      target: &mut [u8],
      cursor: &mut usize,
    ) -> Result<(), GlyphErr> {
      let mut writer = ObjGlyphSerializer::new(
        None,
        Some("TestStruct"),
        None,
        None,
        true,
        true,
        self.glyph_len(),
        target,
        cursor,
      )?;
      writer.add_field(Some("age"), &self.age)?;
      writer.add_field(Some("name"), &self.name)?;
      writer.finish()
    }

    fn glyph_len(&self) -> usize {
      if let Ok(mut calc) =
        ObjGlyphLenCalc::new(false, Some("TestStruct"), None, false, true)
      {
        calc
          .add_field(Some("age"), self.age.glyph_len())
          .unwrap_or_default();
        calc
          .add_field(Some("name"), self.name.glyph_len())
          .unwrap_or_default();
        calc.finish()
      } else {
        0
      }
    }
  }

  /// Tests encoding of object glyphs.
  ///
  /// This test currently provides somewhat limited coverage and could be
  /// improved.  Options:
  ///
  /// - Refer to tests in `serde-glyphs` for some coverage cases.
  /// - Better testing of (optional) sorting by field name bytes.
  #[test]
  fn codec_obj_glyph() {
    // Basic Encoding
    let mut len_calc =
      ObjGlyphLenCalc::new(false, Some("TestType"), None, false, true).unwrap();
    let letters = 'a'..='z';
    for (n, c) in letters.clone().enumerate() {
      len_calc
        .add_field(Some(&c.to_string()), (n as u32).glyph_len())
        .unwrap();
    }
    let len = len_calc.finish();
    std::dbg!(len);

    let mut buffer = std::vec![0u8; len];
    let cursor = &mut 0;
    let mut writer = ObjGlyphSerializer::new(
      None,
      Some("TestType"),
      None,
      None,
      true,
      true,
      letters.size_hint().0,
      &mut buffer,
      cursor,
    )
    .unwrap();
    for (n, c) in letters.clone().enumerate() {
      writer.add_field(Some(&c.to_string()), &(n as u32)).unwrap();
    }
    writer.finish().unwrap();

    let obj_glyph = Glyph::read(&buffer, &mut 0).unwrap();
    let decoded = ObjGlyph::from_glyph(obj_glyph).unwrap();
    std::dbg!(&decoded);

    for (n, c) in letters.clone().enumerate() {
      let field_name = c.to_string();
      let expected_value = n as u32;

      let field = decoded.by_name(&field_name).unwrap();
      let observed_value = u32::from_glyph(field).unwrap();
      assert_eq!(expected_value, observed_value);
    }
  }
}
