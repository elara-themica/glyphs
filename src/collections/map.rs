//! Glyph (de-)serialization for the [`BTreeMap`] type and the dynamic
//! [`MapGlyph`].

use crate::{
  dynamic::DynGlyph,
  glyph_close, glyph_read,
  zerocopy::{round_to_word, ZeroCopy, U32},
  FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader, GlyphOffset,
  GlyphType, ParsedGlyph, ToGlyph,
};
use alloc::collections::BTreeMap;
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
};

/// The specific type header for map glyphs.  Currently, this is identical to
/// the header for [`VecGlyph`].
///
/// - `format_version` must be equal to zero (experimental version)
/// - `reserved` must be equal to zero.
/// - `num_items` indicates the number of glyphs contained in the `VecGlyph`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
pub(crate) struct MapGlyphHeader {
  num_items: U32,
  reserved:  [u8; 4],
}

impl MapGlyphHeader {
  /// Creates a new type-specific header for a [`MapGlyph`].
  ///
  /// As the values for `format_version` and `reserved` are fixed, only the
  /// number of glyphs present in the `VecGlyph` must be specified.
  pub(crate) fn new(num_items: usize) -> Result<MapGlyphHeader, GlyphErr> {
    let num_items = u32::try_from(num_items)
      .map_err(|_e| GlyphErr::MapLenOverflow { num_items })?;
    Ok(MapGlyphHeader {
      num_items: U32::from(num_items),
      reserved:  Default::default(),
    })
  }

  pub(crate) fn num_items(&self) -> usize {
    self.num_items.get() as usize
  }
}

/// SAFETY: Components are all ZeroCopy
unsafe impl ZeroCopy for MapGlyphHeader {}

#[cfg(feature = "alloc")]
impl<K, V> ToGlyph for BTreeMap<K, V>
where
  K: ToGlyph,
  V: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut mgs = MapGlyphSerializer::new(self.len(), target, cursor)?;
    for (key, value) in self.iter() {
      mgs.add_item(key, value)?;
    }
    mgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut mglc = MapGlyphLenCalc::new();
    for (key, value) in self.iter() {
      mglc.add_item(key.glyph_len(), value.glyph_len());
    }
    mglc.finish()
  }
}

/// A glyph-based associative array.
pub struct MapGlyph<G>
where
  G: Glyph,
{
  glyph:   G,
  offsets: NonNull<[GlyphOffset]>,
}

impl<G> FromGlyph<G> for MapGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.confirm_type(GlyphType::Map) {
      return Err(err.into_fge(source));
    }

    let content = source.content_padded();
    let cursor = &mut 0;

    let mgh = match MapGlyphHeader::bbrf(content, cursor) {
      Ok(mgh) => mgh,
      Err(err) => return Err(err.into_fge(source)),
    };
    let offsets = match GlyphOffset::bbrfs(content, cursor, mgh.num_items()) {
      Ok(offsets) => offsets,
      Err(err) => return Err(err.into_fge(source)),
    };

    // Keep internal self references
    let offsets = NonNull::from(offsets);
    Ok(Self {
      glyph: source,
      offsets,
    })
  }
}

impl<G> MapGlyph<G>
where
  G: Glyph,
{
  /// Gives the self-reference to offsets with the lifetime of &self.
  fn offsets(&self) -> &[GlyphOffset] {
    // SAFETY: Guaranteed by trait bounds on G
    unsafe { self.offsets.as_ref() }
  }

  /// Returns the number of entries in the map
  pub fn len(&self) -> usize {
    self.offsets().len()
  }

  /// Returns true iff the map has no entries.
  pub fn is_empty(&self) -> bool {
    self.offsets().len() == 0
  }

  /// Returns the _index_-th Key/Value pair.
  pub fn get(&self, index: usize) -> Option<(ParsedGlyph, ParsedGlyph)> {
    let offset = self.offsets().get(index)?;
    let content = self.glyph.content_padded();
    let mut cursor = offset.cursor(0);
    let key = glyph_read(content, &mut cursor).ok()?;
    let value = glyph_read(content, &mut cursor).ok()?;
    Some((key, value))
  }

  /// Returns an iterator over the contained key/value pairs.
  ///
  /// Note that, currently, the ordering of these values is not strongly
  /// defined; however, they will often be in the expected order based on the
  /// container from which they were originally serialized.
  pub fn iter(
    &self,
  ) -> impl Iterator<Item = (ParsedGlyph<'_>, ParsedGlyph<'_>)>
       + Clone
       + DoubleEndedIterator
       + ExactSizeIterator {
    IterMap {
      offsets: self.offsets(),
      content: self.glyph.content_padded(),
    }
  }
}

impl<'a> MapGlyph<ParsedGlyph<'a>> {
  /// Returns the _index_-th Key/Value pair with lifetimes bound only to the
  /// glyph's backing buffer.
  pub fn get_parsed(
    &self,
    index: usize,
  ) -> Option<(ParsedGlyph<'a>, ParsedGlyph<'a>)> {
    let offset = self.offsets().get(index)?;
    let content = self.glyph.content_padded_parsed();
    let mut cursor = offset.cursor(0);
    let key = glyph_read(content, &mut cursor).ok()?;
    let value = glyph_read(content, &mut cursor).ok()?;
    Some((key, value))
  }

  /// Returns an iterator over the contained key/value pairs, but with lifetimes
  /// bound to the underlying byte buffer.
  ///
  /// Note that, currently, the ordering of these values is not strongly
  /// defined; however, they will often be in the expected order based on the
  /// container from which they were originally serialized.
  pub fn iter_parsed(
    &self,
  ) -> impl Iterator<Item = (ParsedGlyph<'a>, ParsedGlyph<'a>)>
       + Clone
       + DoubleEndedIterator
       + ExactSizeIterator {
    IterMap {
      // SAFETY: Bounds on G
      offsets: unsafe { self.offsets.as_ref() },
      content: self.glyph.content_padded_parsed(),
    }
  }
}

impl<G> Debug for MapGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    f.write_str("MapGlyph")?;
    let mut df = f.debug_map();
    for (key, val) in self.iter() {
      let key = DynGlyph::from_glyph_u(key);
      let val = DynGlyph::from_glyph_u(val);
      df.entry(&key, &val);
    }
    df.finish()
  }
}

/// Iterates through the entries of a [`MapGlyph`]
#[derive(Copy, Clone)]
pub(crate) struct IterMap<'a> {
  offsets: &'a [GlyphOffset],
  content: &'a [u8],
}

impl<'a> Iterator for IterMap<'a> {
  type Item = (ParsedGlyph<'a>, ParsedGlyph<'a>);

  fn next(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_first()?;
    self.offsets = remainder;

    let mut cursor = offset.cursor(0);
    let key = glyph_read(self.content, &mut cursor).ok()?;
    let value = glyph_read(self.content, &mut cursor).ok()?;
    Some((key, value))
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.len();
    (len, Some(len))
  }
}

impl<'a> ExactSizeIterator for IterMap<'a> {
  fn len(&self) -> usize {
    self.offsets.len()
  }
}

impl<'a> DoubleEndedIterator for IterMap<'a> {
  fn next_back(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_last()?;
    self.offsets = remainder;

    let mut cursor = offset.cursor(0);
    let key = glyph_read(self.content, &mut cursor).ok()?;
    let value = glyph_read(self.content, &mut cursor).ok()?;
    Some((key, value))
  }
}

#[derive(Default)]
pub(crate) struct MapGlyphLenCalc {
  num_items: usize,
  items_len: usize,
}

impl MapGlyphLenCalc {
  pub fn new() -> Self {
    Default::default()
  }

  /// Increases the number of items and adds the lengths of the key and value.
  pub fn add_item(&mut self, key_len: usize, value_len: usize) {
    self.add_key(key_len);
    self.add_value(value_len);
  }

  /// Increases the number of items and adds the length of the key.
  pub fn add_key(&mut self, key_len: usize) {
    self.num_items = self.num_items.saturating_add(1);
    self.items_len = self.items_len.saturating_add(key_len);
  }

  /// Adds the length of the value
  pub fn add_value(&mut self, value_len: usize) {
    self.items_len = self.items_len.saturating_add(value_len);
  }

  /// Returns the total length of the [`MapGlyph`]
  pub fn finish(self) -> usize {
    size_of::<GlyphHeader>()
      + round_to_word(
        size_of::<MapGlyphHeader>() + size_of::<GlyphOffset>() * self.num_items,
      )
      + self.items_len
  }
}

pub(crate) struct MapGlyphSerializer<'a> {
  target:         &'a mut [u8],
  cursor:         &'a mut usize,
  glyph_start:    usize,
  content_start:  usize,
  offsets_cursor: usize,
}

impl<'a> MapGlyphSerializer<'a> {
  pub fn new(
    len: usize,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    let glyph_start = GlyphHeader::skip(cursor);
    let content_start = *cursor;
    MapGlyphHeader::new(len)?.bbwr(target, cursor)?;
    let offsets_cursor = GlyphOffset::skip(target, cursor, len, true)?;
    Ok(Self {
      target,
      cursor,
      glyph_start,
      content_start,
      offsets_cursor,
    })
  }

  pub fn add_item<K: ToGlyph, V: ToGlyph>(
    &mut self,
    key: &K,
    value: &V,
  ) -> Result<(), GlyphErr> {
    self.add_key(key)?;
    self.add_value(value)
  }

  pub fn add_key<K: ToGlyph>(&mut self, key: &K) -> Result<(), GlyphErr> {
    GlyphOffset::new(self.content_start, *self.cursor)?
      .bbwr(self.target, &mut self.offsets_cursor)?;
    key.glyph_encode(self.target, self.cursor)
  }

  pub fn add_value<V: ToGlyph>(&mut self, value: &V) -> Result<(), GlyphErr> {
    value.glyph_encode(self.target, self.cursor)
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    glyph_close(
      GlyphType::Map,
      self.target,
      self.glyph_start,
      self.cursor,
      false,
    )?;
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::glyph::glyph_new;

  /// Basic encoding and decoding test.
  #[test]
  fn map_glyph_codec() -> Result<(), GlyphErr> {
    // === Test Basic Encoding and Decoding ===
    let mut map = BTreeMap::new();
    map.insert("Liara", "T'Soni");
    map.insert("Garrus", "Vakarian");
    map.insert("Mordin", "Solus");
    map.insert("Urdnot", "Wrex");
    map.insert("Miranda", "Lawson");
    map.insert("Thane", "Krios");
    // std::dbg!(&map);

    let glyph = glyph_new(&map)?;
    // std::dbg!(&glyph);

    let decoded = MapGlyph::from_glyph(glyph)?;
    // std::dbg!(&map_glyph);

    // Checking Values (and sorted order)
    for ((glyph_key, glyph_value), (orig_key, orig_value)) in
      decoded.iter().zip(map.iter())
    {
      let decoded_key = <&str>::from_glyph(glyph_key)?;
      let decoded_value = <&str>::from_glyph(glyph_value)?;
      assert_eq!(decoded_key, *orig_key);
      assert_eq!(decoded_value, *orig_value);
    }

    Ok(())
  }
}
