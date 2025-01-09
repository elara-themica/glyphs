//! Glyph (de-)serialization for tuples and the dynamic [`TupleGlyph`].

use crate::{
  glyph_close, glyph_read, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  ParsedGlyph, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
};

impl<'a, A, B> ToGlyph for (A, B)
where
  A: ToGlyph,
  B: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut tgs = TupleGlyphSerializer::new(target, cursor)?;
    tgs.add_item(&self.0)?;
    tgs.add_item(&self.1)?;
    tgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut tglc = TupleGlyphLenCalc::new();
    tglc.add_item(self.0.glyph_len());
    tglc.add_item(self.1.glyph_len());
    tglc.finish()
  }
}

impl<A, B, C> ToGlyph for (A, B, C)
where
  A: ToGlyph,
  B: ToGlyph,
  C: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut tgs = TupleGlyphSerializer::new(target, cursor)?;
    tgs.add_item(&self.0)?;
    tgs.add_item(&self.1)?;
    tgs.add_item(&self.2)?;
    tgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut tglc = TupleGlyphLenCalc::new();
    tglc.add_item(self.0.glyph_len());
    tglc.add_item(self.1.glyph_len());
    tglc.add_item(self.2.glyph_len());
    tglc.finish()
  }
}

impl<A, B, C, D> ToGlyph for (A, B, C, D)
where
  A: ToGlyph,
  B: ToGlyph,
  C: ToGlyph,
  D: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut tgs = TupleGlyphSerializer::new(target, cursor)?;
    tgs.add_item(&self.0)?;
    tgs.add_item(&self.1)?;
    tgs.add_item(&self.2)?;
    tgs.add_item(&self.3)?;
    tgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut tglc = TupleGlyphLenCalc::new();
    tglc.add_item(self.0.glyph_len());
    tglc.add_item(self.1.glyph_len());
    tglc.add_item(self.2.glyph_len());
    tglc.add_item(self.3.glyph_len());
    tglc.finish()
  }
}

impl<A, B, C, D, E> ToGlyph for (A, B, C, D, E)
where
  A: ToGlyph,
  B: ToGlyph,
  C: ToGlyph,
  D: ToGlyph,
  E: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut tgs = TupleGlyphSerializer::new(target, cursor)?;
    tgs.add_item(&self.0)?;
    tgs.add_item(&self.1)?;
    tgs.add_item(&self.2)?;
    tgs.add_item(&self.3)?;
    tgs.add_item(&self.4)?;
    tgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut tglc = TupleGlyphLenCalc::new();
    tglc.add_item(self.0.glyph_len());
    tglc.add_item(self.1.glyph_len());
    tglc.add_item(self.2.glyph_len());
    tglc.add_item(self.3.glyph_len());
    tglc.add_item(self.4.glyph_len());
    tglc.finish()
  }
}

impl<A, B, C, D, E, F> ToGlyph for (A, B, C, D, E, F)
where
  A: ToGlyph,
  B: ToGlyph,
  C: ToGlyph,
  D: ToGlyph,
  E: ToGlyph,
  F: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let mut tgs = TupleGlyphSerializer::new(target, cursor)?;
    tgs.add_item(&self.0)?;
    tgs.add_item(&self.1)?;
    tgs.add_item(&self.2)?;
    tgs.add_item(&self.3)?;
    tgs.add_item(&self.4)?;
    tgs.add_item(&self.5)?;
    tgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let mut tglc = TupleGlyphLenCalc::new();
    tglc.add_item(self.0.glyph_len());
    tglc.add_item(self.1.glyph_len());
    tglc.add_item(self.2.glyph_len());
    tglc.add_item(self.3.glyph_len());
    tglc.add_item(self.4.glyph_len());
    tglc.add_item(self.5.glyph_len());
    tglc.finish()
  }
}

/// A glyph containing a series of other glyphs.
///
/// A `TupleGlyph` differs from a [`VecGlyph`] in that the latter has an offsets
/// table to facilitate quick access for large vectors, whereas the random
/// access overhead for a `TupleGlyph` is `O(n)`, like a linked list, due to
/// the variable length of each contained item.
pub struct TupleGlyph<T>(T)
where
  T: Glyph;

impl<T> TupleGlyph<T>
where
  T: Glyph,
{
  /// Returns the `index`-th item in the Tuple Glyph.
  ///
  /// Random access to items in `TupleGlyph`s takes `O(n)` time, as the position
  /// of the `n`-th item can only be determined by checking the length of all
  /// the (variable-length) items preceding it.
  ///
  /// Typically, an entire `TupleGlyph` can be decoded more efficiently by using
  /// the `FromGlyph` trait on the target tuple type.
  pub fn get(&self, index: usize) -> Result<ParsedGlyph<'_>, GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    for _ in 0..index {
      let _ = glyph_read(content, cursor)?;
    }
    glyph_read(content, cursor)
  }

  /// Decodes a 1-tuple
  pub fn single<'g, A: FromGlyph<ParsedGlyph<'g>>>(
    &'g self,
  ) -> Result<A, GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok(A::from_glyph(glyph_read(content, cursor)?)?)
  }

  /// Decodes a 2-tuple
  pub fn double<
    'g,
    A: FromGlyph<ParsedGlyph<'g>>,
    B: FromGlyph<ParsedGlyph<'g>>,
  >(
    &'g self,
  ) -> Result<(A, B), GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 3-tuple
  pub fn triple<
    'g,
    A: FromGlyph<ParsedGlyph<'g>>,
    B: FromGlyph<ParsedGlyph<'g>>,
    C: FromGlyph<ParsedGlyph<'g>>,
  >(
    &'g self,
  ) -> Result<(A, B, C), GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 4-tuple
  pub fn quadruple<
    'g,
    A: FromGlyph<ParsedGlyph<'g>>,
    B: FromGlyph<ParsedGlyph<'g>>,
    C: FromGlyph<ParsedGlyph<'g>>,
    D: FromGlyph<ParsedGlyph<'g>>,
  >(
    &'g self,
  ) -> Result<(A, B, C, D), GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 5-tuple
  pub fn quintuple<
    'g,
    A: FromGlyph<ParsedGlyph<'g>>,
    B: FromGlyph<ParsedGlyph<'g>>,
    C: FromGlyph<ParsedGlyph<'g>>,
    D: FromGlyph<ParsedGlyph<'g>>,
    E: FromGlyph<ParsedGlyph<'g>>,
  >(
    &'g self,
  ) -> Result<(A, B, C, D, E), GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
      E::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 6-tuple
  pub fn sextuple<
    'g,
    A: FromGlyph<ParsedGlyph<'g>>,
    B: FromGlyph<ParsedGlyph<'g>>,
    C: FromGlyph<ParsedGlyph<'g>>,
    D: FromGlyph<ParsedGlyph<'g>>,
    E: FromGlyph<ParsedGlyph<'g>>,
    F: FromGlyph<ParsedGlyph<'g>>,
  >(
    &'g self,
  ) -> Result<(A, B, C, D, E, F), GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
      E::from_glyph(glyph_read(content, cursor)?)?,
      F::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Iterate through the elements of the tuple.
  pub fn iter(&self) -> impl Iterator<Item = ParsedGlyph<'_>> {
    let content = self.0.content_padded();
    IterTuple(content, 0)
  }
}

impl<'a> TupleGlyph<ParsedGlyph<'a>> {
  /// Iterate through the elements of the tuple, but with the resulting
  /// lifetimes bound to the underlying byte buffer.
  pub fn iter_parsed(&self) -> impl Iterator<Item = ParsedGlyph<'a>> {
    let content = self.0.content_parsed();
    IterTuple(content, 0)
  }

  /// Decodes a 1-tuple
  pub fn single_parsed<A: FromGlyph<ParsedGlyph<'a>>>(
    &self,
  ) -> Result<A, GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok(A::from_glyph(glyph_read(content, cursor)?)?)
  }

  /// Decodes a 2-tuple
  pub fn double_parsed<
    A: FromGlyph<ParsedGlyph<'a>>,
    B: FromGlyph<ParsedGlyph<'a>>,
  >(
    &self,
  ) -> Result<(A, B), GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 3-tuple
  pub fn triple_parsed<
    A: FromGlyph<ParsedGlyph<'a>>,
    B: FromGlyph<ParsedGlyph<'a>>,
    C: FromGlyph<ParsedGlyph<'a>>,
  >(
    &self,
  ) -> Result<(A, B, C), GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 4-tuple
  pub fn quadruple_parsed<
    A: FromGlyph<ParsedGlyph<'a>>,
    B: FromGlyph<ParsedGlyph<'a>>,
    C: FromGlyph<ParsedGlyph<'a>>,
    D: FromGlyph<ParsedGlyph<'a>>,
  >(
    &self,
  ) -> Result<(A, B, C, D), GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 5-tuple
  pub fn quintuple_parsed<
    A: FromGlyph<ParsedGlyph<'a>>,
    B: FromGlyph<ParsedGlyph<'a>>,
    C: FromGlyph<ParsedGlyph<'a>>,
    D: FromGlyph<ParsedGlyph<'a>>,
    E: FromGlyph<ParsedGlyph<'a>>,
  >(
    &self,
  ) -> Result<(A, B, C, D, E), GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
      E::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Decodes a 6-tuple
  pub fn sextuple_parsed<
    A: FromGlyph<ParsedGlyph<'a>>,
    B: FromGlyph<ParsedGlyph<'a>>,
    C: FromGlyph<ParsedGlyph<'a>>,
    D: FromGlyph<ParsedGlyph<'a>>,
    E: FromGlyph<ParsedGlyph<'a>>,
    F: FromGlyph<ParsedGlyph<'a>>,
  >(
    &self,
  ) -> Result<(A, B, C, D, E, F), GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(glyph_read(content, cursor)?)?,
      B::from_glyph(glyph_read(content, cursor)?)?,
      C::from_glyph(glyph_read(content, cursor)?)?,
      D::from_glyph(glyph_read(content, cursor)?)?,
      E::from_glyph(glyph_read(content, cursor)?)?,
      F::from_glyph(glyph_read(content, cursor)?)?,
    ))
  }

  /// Returns the `index`-th item in the Tuple Glyph.
  ///
  /// Random access to items in `TupleGlyph`s takes `O(n)` time, as the position
  /// of the `n`-th item can only be determined by checking the length of all
  /// the (variable-length) items preceding it.
  ///
  /// Typically, an entire `TupleGlyph` can be decoded more efficiently by using
  /// the `FromGlyph` trait on the target tuple type.
  pub fn get_parsed(&self, index: usize) -> Result<ParsedGlyph<'a>, GlyphErr> {
    let content = self.0.content_padded_parsed();
    let cursor = &mut 0;
    for _ in 0..index {
      let _ = glyph_read(content, cursor)?;
    }
    glyph_read(content, cursor)
  }
}

impl<T> Debug for TupleGlyph<T>
where
  T: Glyph,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_tuple("TupleGlyph");
    for glyph in self.iter() {
      df.field(&glyph);
    }
    df.finish()
  }
}

impl<T> FromGlyph<T> for TupleGlyph<T>
where
  T: Glyph,
{
  fn from_glyph(source: T) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;
    Ok(TupleGlyph(source))
  }
}

impl<'a, A, B> FromGlyph<ParsedGlyph<'a>> for (A, B)
where
  A: FromGlyph<ParsedGlyph<'a>>,
  B: FromGlyph<ParsedGlyph<'a>>,
{
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;

    let content = source.content_parsed();
    let cursor = &mut 0;
    let a = glyph_read(content, cursor)?;
    let b = glyph_read(content, cursor)?;

    let a = A::from_glyph(a)?;
    let b = B::from_glyph(b)?;

    Ok((a, b))
  }
}

impl<'a, A, B, C> FromGlyph<ParsedGlyph<'a>> for (A, B, C)
where
  A: FromGlyph<ParsedGlyph<'a>>,
  B: FromGlyph<ParsedGlyph<'a>>,
  C: FromGlyph<ParsedGlyph<'a>>,
{
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;

    let content = source.content_parsed();
    let cursor = &mut 0;
    let a = glyph_read(content, cursor)?;
    let b = glyph_read(content, cursor)?;
    let c = glyph_read(content, cursor)?;

    let a = A::from_glyph(a)?;
    let b = B::from_glyph(b)?;
    let c = C::from_glyph(c)?;

    Ok((a, b, c))
  }
}

impl<'a, A, B, C, D> FromGlyph<ParsedGlyph<'a>> for (A, B, C, D)
where
  A: FromGlyph<ParsedGlyph<'a>>,
  B: FromGlyph<ParsedGlyph<'a>>,
  C: FromGlyph<ParsedGlyph<'a>>,
  D: FromGlyph<ParsedGlyph<'a>>,
{
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;

    let content = source.content_parsed();
    let cursor = &mut 0;
    let a = glyph_read(content, cursor)?;
    let b = glyph_read(content, cursor)?;
    let c = glyph_read(content, cursor)?;
    let d = glyph_read(content, cursor)?;

    let a = A::from_glyph(a)?;
    let b = B::from_glyph(b)?;
    let c = C::from_glyph(c)?;
    let d = D::from_glyph(d)?;

    Ok((a, b, c, d))
  }
}

impl<'a, A, B, C, D, E> FromGlyph<ParsedGlyph<'a>> for (A, B, C, D, E)
where
  A: FromGlyph<ParsedGlyph<'a>>,
  B: FromGlyph<ParsedGlyph<'a>>,
  C: FromGlyph<ParsedGlyph<'a>>,
  D: FromGlyph<ParsedGlyph<'a>>,
  E: FromGlyph<ParsedGlyph<'a>>,
{
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;

    let content = source.content_parsed();
    let cursor = &mut 0;
    let a = glyph_read(content, cursor)?;
    let b = glyph_read(content, cursor)?;
    let c = glyph_read(content, cursor)?;
    let d = glyph_read(content, cursor)?;
    let e = glyph_read(content, cursor)?;

    let a = A::from_glyph(a)?;
    let b = B::from_glyph(b)?;
    let c = C::from_glyph(c)?;
    let d = D::from_glyph(d)?;
    let e = E::from_glyph(e)?;

    Ok((a, b, c, d, e))
  }
}

impl<'a, A, B, C, D, E, F> FromGlyph<ParsedGlyph<'a>> for (A, B, C, D, E, F)
where
  A: FromGlyph<ParsedGlyph<'a>>,
  B: FromGlyph<ParsedGlyph<'a>>,
  C: FromGlyph<ParsedGlyph<'a>>,
  D: FromGlyph<ParsedGlyph<'a>>,
  E: FromGlyph<ParsedGlyph<'a>>,
  F: FromGlyph<ParsedGlyph<'a>>,
{
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Tuple)?;

    let content = source.content_parsed();
    let cursor = &mut 0;
    let a = glyph_read(content, cursor)?;
    let b = glyph_read(content, cursor)?;
    let c = glyph_read(content, cursor)?;
    let d = glyph_read(content, cursor)?;
    let e = glyph_read(content, cursor)?;
    let f = glyph_read(content, cursor)?;

    let a = A::from_glyph(a)?;
    let b = B::from_glyph(b)?;
    let c = C::from_glyph(c)?;
    let d = D::from_glyph(d)?;
    let e = E::from_glyph(e)?;
    let f = F::from_glyph(f)?;

    Ok((a, b, c, d, e, f))
  }
}

/// An iterator through the glyphs in a [`TupleGlyph`].
pub(crate) struct IterTuple<'a>(&'a [u8], usize);

impl<'a> Iterator for IterTuple<'a> {
  type Item = ParsedGlyph<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    match glyph_read(self.0, &mut self.1) {
      Ok(glyph_ref) => Some(glyph_ref),
      Err(_) => None,
    }
  }
}

#[derive(Default)]
pub(crate) struct TupleGlyphLenCalc(usize);

impl TupleGlyphLenCalc {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn add_item(&mut self, item_len: usize) {
    self.0 = self.0.saturating_add(item_len);
  }

  pub fn finish(self) -> usize {
    size_of::<GlyphHeader>() + self.0
  }
}

pub(crate) struct TupleGlyphSerializer<'a> {
  target:      &'a mut [u8],
  cursor:      &'a mut usize,
  glyph_start: usize,
}

impl<'a> TupleGlyphSerializer<'a> {
  pub fn new(
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    let glyph_start = GlyphHeader::skip(cursor);
    Ok(Self {
      target,
      cursor,
      glyph_start,
    })
  }

  pub fn add_item<T: ToGlyph>(&mut self, item: &T) -> Result<(), GlyphErr> {
    item.glyph_encode(self.target, self.cursor)
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    glyph_close(
      GlyphType::Tuple,
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
  use ::test::Bencher;
  use std::hint::black_box;

  const BENCH_BUF_SIZE: usize = 8192;

  /// Verify the correct encoding and decoding for tuples of length 2-6.
  #[test]
  fn codec_glyph_tuple() -> Result<(), GlyphErr> {
    let (a, b, c, d, e, f) = (8, 6, 7, 5, 3, 0);

    let ab = glyph_new(&(a, b))?;
    let abc = glyph_new(&(a, b, c))?;
    let abcd = glyph_new(&(a, b, c, d))?;
    let abcde = glyph_new(&(a, b, c, d, e))?;
    let abcdef = glyph_new(&(a, b, c, d, e, f))?;

    let (aa, bb) = <(i32, i32)>::from_glyph(ab.borrow())?;
    assert_eq!((a, b), (aa, bb));
    let (aa, bb, cc) = <(i32, i32, i32)>::from_glyph(abc.borrow())?;
    assert_eq!((aa, bb, cc), (a, b, c));
    let (aa, bb, cc, dd) = <(i32, i32, i32, i32)>::from_glyph(abcd.borrow())?;
    assert_eq!((aa, bb, cc, dd), (a, b, c, d));
    let (aa, bb, cc, dd, ee) =
      <(i32, i32, i32, i32, i32)>::from_glyph(abcde.borrow())?;
    assert_eq!((aa, bb, cc, dd, ee), (a, b, c, d, e));
    let (aa, bb, cc, dd, ee, ff) =
      <(i32, i32, i32, i32, i32, i32)>::from_glyph(abcdef.borrow())?;
    assert_eq!((aa, bb, cc, dd, ee, ff), (a, b, c, d, e, f));

    let tg = TupleGlyph::from_glyph(abcdef)?;

    // Test `TupleGlyph::get()`
    assert_eq!(i32::from_glyph(tg.get(0)?), Ok(8));
    assert_eq!(i32::from_glyph(tg.get(1)?), Ok(6));
    assert_eq!(i32::from_glyph(tg.get(2)?), Ok(7));
    assert_eq!(i32::from_glyph(tg.get(3)?), Ok(5));
    assert_eq!(i32::from_glyph(tg.get(4)?), Ok(3));
    assert_eq!(i32::from_glyph(tg.get(5)?), Ok(0));
    assert!(tg.get(6).is_err());

    let mut sum = 0;
    for glyph in tg.iter() {
      sum += i32::from_glyph(glyph)?;
    }
    assert_eq!(sum, 8 + 6 + 7 + 5 + 3);
    Ok(())
  }

  /// Benchmark the encoding of a short tuple glyph.
  ///
  /// This should be close to the worst case for encoding tuple glyphs, with
  /// a separate object to write every 4 bytes.
  #[bench]
  fn enc_glyph_tuple(b: &mut Bencher) {
    let mut buf = [0; BENCH_BUF_SIZE];
    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| unsafe {
      let cursor = &mut 0;
      black_box(buf);
      for _ in 0..256 {
        ((), (), ())
          .glyph_encode(&mut buf[..], cursor)
          .unwrap_unchecked()
      }
      black_box(buf);
      Ok::<(), GlyphErr>(())
    })
  }

  /// Benchmark the decoding of short tuple glyph.
  ///
  /// This should be close to the worst case for decoding tuple glyphs, with
  /// a separate object to parse every 4 bytes.
  #[bench]
  fn dec_glyph_tuple(b: &mut Bencher) {
    let mut buf = [0u8; BENCH_BUF_SIZE];
    let cursor = &mut 0;
    for _ in 0..256 {
      ((), (), ()).glyph_encode(&mut buf[..], cursor).unwrap();
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..256 {
        let tg = glyph_read(&buf, cursor)?;
        let (a, b, c): ((), (), ()) = FromGlyph::from_glyph(tg)?;
        black_box((a, b, c));
      }
      Ok::<(), GlyphErr>(())
    })
  }
}
