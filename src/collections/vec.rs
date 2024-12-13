//! Glyph (de-)serialization for arrays, slices, and vectors, as well as the
//! dynamic [`VecGlyph`].
//!
//! The format of vector glyphs is as follows:
//! - A [`GlyphHeader`]
//! - A [`VecGlyphHeader`], which includes the number of items in the
//!   vector glyph.
//! - An array of [`U32`]s, giving the offset of each item from the start
//!   of the items buffer.  Note that this array is the official list of
//!   items--technically, multiple items could refer to the same
//!   underlying bytes if they contain the same offset.
//! - The remaining bytes of the glyph are a buffer for the glyphs it
//!   contains.
use crate::{
  glyph_close, glyph_read,
  util::debug::CloneDebugIterator,
  zerocopy::{ZeroCopy, U32},
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphOffset, GlyphType, ParsedGlyph,
  ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
};

/// The specific type header for (non-primitive) vector glyphs.
///
/// - `format_version` must be equal to zero (experimental version)
/// - `reserved` must be equal to zero.
/// - `num_items` indicates the number of glyphs contained in the `VecGlyph`.
#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub(crate) struct VecGlyphHeader {
  format_version: u8,
  reserved:       [u8; 3],
  num_items:      U32,
}

unsafe impl ZeroCopy for VecGlyphHeader {}

impl VecGlyphHeader {
  /// Creates a new type-specific header for a [`VecGlyph`].
  ///
  /// As the values for `format_version` and `reserved` are fixed, only the
  /// number of glyphs present in the `VecGlyph` must be specified.
  pub fn new(num_items: usize) -> Result<VecGlyphHeader, GlyphErr> {
    let num_items = u32::try_from(num_items)
      .map_err(|_e| GlyphErr::VecGlyphLenOverflow { num_items })?;
    Ok(VecGlyphHeader {
      format_version: 0,
      reserved:       [0; 3],
      num_items:      U32::from(num_items),
    })
  }

  /// Returns the number of items contained in the VecGlyph.
  pub fn num_items(&self) -> usize {
    self.num_items.get() as usize
  }
}

/// Vectors of primitives and very common types with fixed-length
/// representations may have a more specific implementation.  This `impl`
/// is the default used for all other types (e.g., `str`).
impl<T> ToGlyph for [T]
where
  T: ToGlyph,
{
  default fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut vgs = VecGlyphSerializer::new(self.len(), target, cursor)?;
    for field in self.iter() {
      vgs.add_field(field)?;
    }
    vgs.finish()
  }

  default fn glyph_len(&self) -> usize {
    let mut vglc = VecGlyphLenCalc::new();
    for field in self.iter() {
      vglc.add_item(field.glyph_len());
    }
    vglc.finish()
  }
}

/// A glyph that contains a vector of other glyphs.
pub struct VecGlyph<G>
where
  G: Glyph,
{
  /// The source glyph that is a vector glyph
  glyph: G,

  /// Pointer to the offsets table.
  offsets: NonNull<[GlyphOffset]>,
}

impl<G> VecGlyph<G>
where
  G: Glyph,
{
  /// Returns the number of items (glyphs) in the vector.
  pub fn len(&self) -> usize {
    self.offsets().len()
  }

  /// Returns true iff the `VecGlyph` contains no items.
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the `index`-th glyph in the vector.
  pub fn get(&self, index: usize) -> Option<ParsedGlyph<'_>> {
    let offset = self.offsets().get(index)?;
    let mut cursor = offset.cursor(0);
    match glyph_read(self.glyph.content_padded(), &mut cursor) {
      Ok(glyph) => Some(glyph),
      Err(_) => None,
    }
  }

  /// Returns the `index`-th glyph in the vector, returning an error if the
  /// glyph does not decode correctly.
  pub fn get_checked(
    &self,
    index: usize,
  ) -> Result<Option<ParsedGlyph<'_>>, GlyphErr> {
    if let Some(offset) = self.offsets().get(index) {
      let mut cursor = offset.cursor(0);
      let glyph = glyph_read(self.glyph.content_padded(), &mut cursor)?;
      Ok(Some(glyph))
    } else {
      Ok(None)
    }
  }

  /// An iterator over contained glyphs.
  pub fn iter(
    &self,
  ) -> impl Iterator<Item = ParsedGlyph<'_>>
       + Clone
       + DoubleEndedIterator
       + ExactSizeIterator {
    IterVec {
      offsets: self.offsets(),
      content: self.glyph.content_padded(),
    }
  }

  /// Limits pointer unsafety by immediately binding lifetime to `&'_ self`.
  fn offsets(&self) -> &[GlyphOffset] {
    unsafe { self.offsets.as_ref() } // SAFETY: Guaranteed by trait bounds
  }
}

impl<'a> VecGlyph<ParsedGlyph<'a>> {
  /// Returns the `index`-th glyph in the vector.
  pub fn get_parsed(&self, index: usize) -> Option<ParsedGlyph<'a>> {
    let offset = self.offsets().get(index)?;
    let mut cursor = offset.cursor(0);
    match glyph_read(self.glyph.content_padded_parsed(), &mut cursor) {
      Ok(glyph) => Some(glyph),
      Err(_) => None,
    }
  }

  /// Returns the `index`-th glyph in the vector, returning an error if the
  /// glyph does not decode correctly.
  pub fn get_checked_parsed(
    &self,
    index: usize,
  ) -> Result<Option<ParsedGlyph<'a>>, GlyphErr> {
    if let Some(offset) = self.offsets().get(index) {
      let mut cursor = offset.cursor(0);
      let glyph = glyph_read(self.glyph.content_padded_parsed(), &mut cursor)?;
      Ok(Some(glyph))
    } else {
      Ok(None)
    }
  }

  /// An iterator over contained glyphs.
  pub fn iter_parsed(&self) -> impl Iterator<Item = ParsedGlyph<'a>> + Clone {
    unsafe {
      IterVec {
        offsets: self.offsets.as_ref(),
        content: self.glyph.content_padded_parsed(),
      }
    }
  }
}

impl<G> FromGlyph<G> for VecGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::VecGlyph)?;
    let contents = source.content_padded();
    let mut cursor = 0;
    let header = VecGlyphHeader::bbrf(contents, &mut cursor)?;
    let offsets = NonNull::from(GlyphOffset::bbrfs(
      contents,
      &mut cursor,
      header.num_items(),
    )?);
    Ok(Self {
      glyph: source,
      offsets,
    })
  }
}

// impl<'a, 'b> IntoIterator for &'a VecGlyph<>

impl<G> Debug for VecGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    if f.alternate() {
      let mut df = f.debug_struct("VecGlyph");
      df.field("glyph_len", &self.glyph.glyph_len());
      df.field("len", &self.len());
      df.field("offsets", &self.offsets());
      df.field("entries", &self.iter().clone_debug());
      df.finish()
    } else {
      let mut df = f.debug_list();
      for i in 0..self.len() {
        let result = self.get(i);
        df.entry(&result);
      }
      df.finish()
    }
  }
}

/// Encodes a `Vec<T>` into a glyph, provided `T` implements `ToGlyph`.
///
/// This is the default implementation when there's not a more specialized
/// version, e.g., that uses a specific type of vector glyph to avoid the
/// overhead of each item being encoded as a glyph, that avoids the per-item
/// overhead of storing individual items as glyphs.  This would be extremely
/// inefficient, for example, for a vector of `u8`
#[cfg(feature = "alloc")]
impl<'a, T> ToGlyph for alloc::vec::Vec<T>
where
  T: ToGlyph,
{
  default fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    (&self[..]).glyph_encode(target, cursor)
  }

  default fn glyph_len(&self) -> usize {
    (self[..]).glyph_len()
  }
}

/// An iterator through the items of a [`VecGlyph`].
#[derive(Copy, Clone)]
struct IterVec<'a> {
  offsets: &'a [GlyphOffset],
  content: &'a [u8],
}

impl<'a> Iterator for IterVec<'a> {
  type Item = ParsedGlyph<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_first()?;
    self.offsets = remainder;
    let mut cursor = offset.cursor(0);
    glyph_read(self.content, &mut cursor).ok()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.len();
    (len, Some(len))
  }
}

impl<'a> ExactSizeIterator for IterVec<'a> {
  fn len(&self) -> usize {
    self.offsets.len()
  }
}

impl<'a> DoubleEndedIterator for IterVec<'a> {
  fn next_back(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_last()?;
    self.offsets = remainder;
    let mut cursor = offset.cursor(0);
    glyph_read(self.content, &mut cursor).ok()
  }
}

#[derive(Default)]
pub(crate) struct VecGlyphLenCalc {
  num_items: usize,
  items_len: usize,
}

impl VecGlyphLenCalc {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn add_item(&mut self, item_len: usize) {
    self.num_items = self.num_items.saturating_add(1);
    self.items_len = self.items_len.saturating_add(item_len);
  }

  pub fn finish(self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<VecGlyphHeader>()
      + GlyphOffset::table_len(self.num_items)
      + self.items_len
  }
}

pub(crate) struct VecGlyphSerializer<'a> {
  target:         &'a mut [u8],
  cursor:         &'a mut usize,
  glyph_start:    usize,
  content_start:  usize,
  offsets_cursor: usize,
}

impl<'a> VecGlyphSerializer<'a> {
  pub fn new(
    len: usize,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    let glyph_start = GlyphHeader::skip(cursor);
    let content_start = *cursor;
    VecGlyphHeader::new(len)?.bbwr(target, cursor)?;
    let offsets_cursor = GlyphOffset::skip(target, cursor, len, true)?;
    Ok(Self {
      target,
      cursor,
      glyph_start,
      content_start,
      offsets_cursor,
    })
  }

  pub fn add_field<T: ToGlyph>(&mut self, field: &T) -> Result<(), GlyphErr> {
    GlyphOffset::new(self.content_start, *self.cursor)?
      .bbwr(self.target, &mut self.offsets_cursor)?;
    field.glyph_encode(self.target, self.cursor)
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    glyph_close(
      GlyphType::VecGlyph,
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
  use crate::{glyph::glyph_new, util::BENCH_BUF_SIZE};
  use ::test::Bencher;
  use alloc::vec::Vec;
  use std::{dbg, println, vec};

  #[test]
  fn codec_glyph_vec() -> Result<(), GlyphErr> {
    let to_encode = vec![
      "I",
      "am",
      "the",
      "very",
      "model",
      "of",
      "a",
      "modern",
      "Major-General",
    ];
    let glyph = glyph_new(&to_encode)?;
    println!("{:?}", &glyph);

    let vg = VecGlyph::from_glyph(glyph)?;
    for (i, glyph) in vg.iter().enumerate() {
      let dec = <&str>::from_glyph(glyph)?;
      assert_eq!(dec, to_encode[i]);
    }

    // Ensure vectors of primitives use their specialized types, rather than
    // the per-item type information.
    let mut num_vec = Vec::new();
    for i in 0..8 {
      num_vec.push(i as u8);
    }
    let vg = glyph_new(&num_vec)?;
    assert_eq!(
      vg.glyph_len(),
      size_of::<GlyphHeader>() + size_of::<VecGlyphHeader>() + num_vec.len()
    );
    Ok(())
  }

  /// Tests the encoding speed for a vector glyph.
  ///
  /// This should be close to the worst-case-scenario for encoding a vector
  /// glyph; 3 items in 64 bytes.
  #[bench]
  fn enc_glyph_vec(b: &mut Bencher) {
    let ga = glyph_new(&1).unwrap();
    let gb = glyph_new(&2).unwrap();
    let gc = glyph_new(&0xbadc_0ffe_e0dd_f00d_u64.to_be()).unwrap();
    let src = vec![ga, gb, gc];

    let mut target: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..128 {
        src.glyph_encode(target.as_mut(), cursor)?;
      }
      Ok::<(), GlyphErr>(())
    });
  }

  /// Tests the decoding speed for a vector glyph.
  ///
  /// This should be close to the worst-case-scenario for decoding a vector
  /// glyph; 3 items in 64 bytes.
  #[bench]
  fn dec_glyph_vec(b: &mut Bencher) {
    let ga = glyph_new(&1).unwrap();
    let gb = glyph_new(&2).unwrap();
    let gc = glyph_new(&3_u64.to_be()).unwrap();
    let src = vec![ga, gb, gc];

    let mut target: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();

    let cursor = &mut 0;
    for _ in 0..128 {
      src.glyph_encode(target.as_mut(), cursor).unwrap();
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..128 {
        let _ = glyph_read(&target, cursor)?;
      }
      Ok::<(), GlyphErr>(())
    });
  }

  #[test]
  fn test_dyn_enc_vec() -> Result<(), GlyphErr> {
    let to_encode: Vec<&dyn ToGlyph> = vec![&42u8, &42i64, &"world"];
    let glyph = glyph_new(&to_encode)?;
    dbg!(&glyph);

    let vg = VecGlyph::from_glyph(glyph.borrow())?;
    let g0 = u8::from_glyph(vg.get(0).unwrap())?;
    assert_eq!(g0, 42);
    let g1 = i64::from_glyph(vg.get(1).unwrap())?;
    assert_eq!(g1, 42);
    let g2 = <&str>::from_glyph(vg.get_parsed(2).unwrap())?;
    drop(vg);
    assert_eq!(g2, "world");
    drop(glyph);

    // Must not compile
    // assert_eq!(g2, "world"); // Compiler error

    Ok(())
  }
}
