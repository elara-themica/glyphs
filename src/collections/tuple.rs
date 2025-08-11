//! Glyph (de-)serialization for tuples and the dynamic [`TupleGlyph`].

use crate::{
  dynamic::DynGlyph, glyph_close, DecodeErr, EncodedGlyph, FromGlyph, Glyph,
  GlyphErr, GlyphHeader, GlyphSorting, GlyphType, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
};
use std::{cmp::Ordering, ops::Deref};

/// A glyph containing a series of other glyphs.
///
/// A `TupleGlyph` differs from a [`VecGlyph`] in that the latter has an offsets
/// table to facilitate quick access for large vectors, whereas the random
/// access overhead for a `TupleGlyph` is `O(n)`, like a linked list, due to
/// the variable length of each contained item.
pub struct TupleGlyph<T>(T)
where
  T: Deref<Target = Glyph>;

impl<T> TupleGlyph<T>
where
  T: Deref<Target = Glyph>,
{
  /// Returns the `index`-th item in the Tuple Glyph.
  ///
  /// Random access to items in `TupleGlyph`s takes `O(n)` time, as the position
  /// of the `n`-th item can only be determined by checking the length of all
  /// the (variable-length) items preceding it.
  ///
  /// Typically, an entire `TupleGlyph` can be decoded more efficiently by using
  /// the `FromGlyph` trait on the target tuple type.
  pub fn get(&self, index: usize) -> Result<&Glyph, GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    for _ in 0..index {
      let _ = Glyph::read(content, cursor)?;
    }
    Glyph::read(content, cursor)
  }

  /// Decodes a 1-tuple
  pub fn single<'g, A>(&'g self) -> Result<A, GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok(
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    )
  }

  /// Decodes a 2-tuple
  pub fn double<'g, A, B>(&'g self) -> Result<(A, B), GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    B: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error> + From<B::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 3-tuple
  pub fn triple<'g, A, B, C>(&'g self) -> Result<(A, B, C), GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    B: FromGlyph<&'g Glyph>,
    C: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error> + From<B::Error> + From<C::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 4-tuple
  pub fn quadruple<'g, A, B, C, D>(&'g self) -> Result<(A, B, C, D), GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    B: FromGlyph<&'g Glyph>,
    C: FromGlyph<&'g Glyph>,
    D: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error> + From<B::Error> + From<C::Error> + From<D::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 5-tuple
  pub fn quintuple<'g, A, B, C, D, E>(
    &'g self,
  ) -> Result<(A, B, C, D, E), GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    B: FromGlyph<&'g Glyph>,
    C: FromGlyph<&'g Glyph>,
    D: FromGlyph<&'g Glyph>,
    E: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error>
      + From<B::Error>
      + From<C::Error>
      + From<D::Error>
      + From<E::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      E::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 6-tuple
  pub fn sextuple<'g, A, B, C, D, E, F>(
    &'g self,
  ) -> Result<(A, B, C, D, E, F), GlyphErr>
  where
    A: FromGlyph<&'g Glyph>,
    B: FromGlyph<&'g Glyph>,
    C: FromGlyph<&'g Glyph>,
    D: FromGlyph<&'g Glyph>,
    E: FromGlyph<&'g Glyph>,
    F: FromGlyph<&'g Glyph>,
    GlyphErr: From<A::Error>
      + From<B::Error>
      + From<C::Error>
      + From<D::Error>
      + From<E::Error>
      + From<F::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      E::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      F::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Iterate through the elements of the tuple.
  pub fn iter(&self) -> impl Iterator<Item = &Glyph> {
    let content = self.0.content_padded();
    IterTuple(content, 0)
  }
}

impl<'a> TupleGlyph<&'a Glyph> {
  /// Iterate through the elements of the tuple, but with the resulting
  /// lifetimes bound to the underlying byte buffer.
  pub fn iter_parsed(&self) -> impl Iterator<Item = &'a Glyph> {
    let content = self.0.content();
    IterTuple(content, 0)
  }

  /// Decodes a 1-tuple
  pub fn single_parsed<A>(&self) -> Result<A, GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok(
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    )
  }

  /// Decodes a 2-tuple
  pub fn double_parsed<A, B>(&self) -> Result<(A, B), GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    B: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error> + From<B::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 3-tuple
  pub fn triple_parsed<A, B, C>(&self) -> Result<(A, B, C), GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    B: FromGlyph<&'a Glyph>,
    C: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error> + From<B::Error> + From<C::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 4-tuple
  pub fn quadruple_parsed<A, B, C, D>(&self) -> Result<(A, B, C, D), GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    B: FromGlyph<&'a Glyph>,
    C: FromGlyph<&'a Glyph>,
    D: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error> + From<B::Error> + From<C::Error> + From<D::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 5-tuple
  pub fn quintuple_parsed<A, B, C, D, E>(
    &self,
  ) -> Result<(A, B, C, D, E), GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    B: FromGlyph<&'a Glyph>,
    C: FromGlyph<&'a Glyph>,
    D: FromGlyph<&'a Glyph>,
    E: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error>
      + From<B::Error>
      + From<C::Error>
      + From<D::Error>
      + From<E::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      E::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
    ))
  }

  /// Decodes a 6-tuple
  pub fn sextuple_parsed<A, B, C, D, E, F>(
    &self,
  ) -> Result<(A, B, C, D, E, F), GlyphErr>
  where
    A: FromGlyph<&'a Glyph>,
    B: FromGlyph<&'a Glyph>,
    C: FromGlyph<&'a Glyph>,
    D: FromGlyph<&'a Glyph>,
    E: FromGlyph<&'a Glyph>,
    F: FromGlyph<&'a Glyph>,
    GlyphErr: From<A::Error>
      + From<B::Error>
      + From<C::Error>
      + From<D::Error>
      + From<E::Error>
      + From<F::Error>,
  {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    Ok((
      A::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      B::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      C::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      D::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      E::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
      F::from_glyph(Glyph::read(content, cursor)?)
        .map_err(|err| GlyphErr::from(err.into_err()))?,
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
  pub fn get_parsed(&self, index: usize) -> Result<&'a Glyph, GlyphErr> {
    let content = self.0.content_padded();
    let cursor = &mut 0;
    for _ in 0..index {
      let _ = Glyph::read(content, cursor)?;
    }
    Glyph::read(content, cursor)
  }
}

impl<T> Debug for TupleGlyph<T>
where
  T: Deref<Target = Glyph>,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_tuple("TupleGlyph");
    for glyph in self.iter() {
      let decoded = DynGlyph::new(glyph);
      df.field(&decoded);
    }
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for TupleGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::TypeAndBytes => {
        GlyphSorting::type_and_bytes(self.0.deref(), other.0.deref())
      },
      GlyphSorting::Experimental => {
        GlyphSorting::dyn_ord(self.0.deref(), other.0.deref(), sorting)
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for TupleGlyph<G> {}

impl<T> FromGlyph<T> for TupleGlyph<T>
where
  T: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: T) -> Result<Self, DecodeErr<T, Self::Error>> {
    match source.header().confirm_type(GlyphType::Tuple) {
      Ok(_) => Ok(TupleGlyph(source)),
      Err(err) => Err(DecodeErr::new(source, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Ord for TupleGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for TupleGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for TupleGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// An iterator through the glyphs in a [`TupleGlyph`].
pub(crate) struct IterTuple<'a>(&'a [u8], usize);

impl<'a> Iterator for IterTuple<'a> {
  type Item = &'a Glyph;

  fn next(&mut self) -> Option<Self::Item> {
    match Glyph::read(self.0, &mut self.1) {
      Ok(glyph_ref) => Some(glyph_ref),
      Err(_) => None,
    }
  }
}

#[doc(hidden)]
#[derive(Default)]
pub struct TupleGlyphLenCalc(usize);

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

#[doc(hidden)]
pub struct TupleGlyphSerializer<'a> {
  target:      &'a mut [u8],
  cursor:      &'a mut usize,
  glyph_start: usize,
}

impl<'a> TupleGlyphSerializer<'a> {
  pub fn new(
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    let glyph_start = *cursor;
    *cursor += size_of::<GlyphHeader>();
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

impl<'a, A, B> FromGlyph<&'a Glyph> for (A, B)
where
  A: FromGlyph<&'a Glyph>,
  B: FromGlyph<&'a Glyph>,
  GlyphErr: From<A::Error> + From<B::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Tuple) {
      return Err(DecodeErr::new(source, err));
    };

    let content = source.content();
    let cursor = &mut 0;
    let a = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let b = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };

    let a =
      A::from_glyph(a).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let b =
      B::from_glyph(b).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;

    Ok((a, b))
  }
}

impl<'a, A, B, C> FromGlyph<&'a Glyph> for (A, B, C)
where
  A: FromGlyph<&'a Glyph>,
  B: FromGlyph<&'a Glyph>,
  C: FromGlyph<&'a Glyph>,
  GlyphErr: From<A::Error> + From<B::Error> + From<C::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Tuple) {
      return Err(DecodeErr::new(source, err));
    };

    let content = source.content();
    let cursor = &mut 0;
    let a = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let b = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let c = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };

    let a =
      A::from_glyph(a).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let b =
      B::from_glyph(b).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let c =
      C::from_glyph(c).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;

    Ok((a, b, c))
  }
}

impl<'a, A, B, C, D> FromGlyph<&'a Glyph> for (A, B, C, D)
where
  A: FromGlyph<&'a Glyph>,
  B: FromGlyph<&'a Glyph>,
  C: FromGlyph<&'a Glyph>,
  D: FromGlyph<&'a Glyph>,
  GlyphErr: From<A::Error> + From<B::Error> + From<C::Error> + From<D::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Tuple) {
      return Err(DecodeErr::new(source, err));
    };

    let content = source.content();
    let cursor = &mut 0;
    let a = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let b = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let c = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let d = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };

    let a =
      A::from_glyph(a).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let b =
      B::from_glyph(b).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let c =
      C::from_glyph(c).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let d =
      D::from_glyph(d).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;

    Ok((a, b, c, d))
  }
}

impl<'a, A, B, C, D, E> FromGlyph<&'a Glyph> for (A, B, C, D, E)
where
  A: FromGlyph<&'a Glyph>,
  B: FromGlyph<&'a Glyph>,
  C: FromGlyph<&'a Glyph>,
  D: FromGlyph<&'a Glyph>,
  E: FromGlyph<&'a Glyph>,
  GlyphErr: From<A::Error>
    + From<B::Error>
    + From<C::Error>
    + From<D::Error>
    + From<E::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Tuple) {
      return Err(DecodeErr::new(source, err));
    };

    let content = source.content();
    let cursor = &mut 0;
    let a = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let b = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let c = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let d = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let e = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };

    let a =
      A::from_glyph(a).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let b =
      B::from_glyph(b).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let c =
      C::from_glyph(c).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let d =
      D::from_glyph(d).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let e =
      E::from_glyph(e).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;

    Ok((a, b, c, d, e))
  }
}

impl<'a, A, B, C, D, E, F> FromGlyph<&'a Glyph> for (A, B, C, D, E, F)
where
  A: FromGlyph<&'a Glyph>,
  B: FromGlyph<&'a Glyph>,
  C: FromGlyph<&'a Glyph>,
  D: FromGlyph<&'a Glyph>,
  E: FromGlyph<&'a Glyph>,
  F: FromGlyph<&'a Glyph>,
  GlyphErr: From<A::Error>
    + From<B::Error>
    + From<C::Error>
    + From<D::Error>
    + From<E::Error>
    + From<F::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(
    source: &'a Glyph,
  ) -> Result<Self, DecodeErr<&'a Glyph, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Tuple) {
      return Err(DecodeErr::new(source, err));
    };

    let content = source.content();
    let cursor = &mut 0;
    let a = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let b = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let c = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let d = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let e = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let f = match Glyph::read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };

    let a =
      A::from_glyph(a).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let b =
      B::from_glyph(b).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let c =
      C::from_glyph(c).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let d =
      D::from_glyph(d).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let e =
      E::from_glyph(e).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;
    let f =
      F::from_glyph(f).map_err(|err| err.map_err(|err| GlyphErr::from(err)))?;

    Ok((a, b, c, d, e, f))
  }
}

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

#[cfg(test)]
mod test {
  use super::*;

  const BENCH_BUF_SIZE: usize = 8192;

  /// Verify the correct encoding and decoding for tuples of length 2-6.
  #[test]
  fn codec_glyph_tuple() {
    let (a, b, c, d, e, f) = (8, 6, 7, 5, 3, 0);

    let ab = Glyph::new(&(a, b)).unwrap();
    let abc = Glyph::new(&(a, b, c)).unwrap();
    let abcd = Glyph::new(&(a, b, c, d)).unwrap();
    let abcde = Glyph::new(&(a, b, c, d, e)).unwrap();
    let abcdef = Glyph::new(&(a, b, c, d, e, f)).unwrap();

    let (aa, bb) = <(i32, i32)>::from_glyph(ab.as_ref()).unwrap();
    assert_eq!((a, b), (aa, bb));
    let (aa, bb, cc) = <(i32, i32, i32)>::from_glyph(abc.as_ref()).unwrap();
    assert_eq!((aa, bb, cc), (a, b, c));
    let (aa, bb, cc, dd) =
      <(i32, i32, i32, i32)>::from_glyph(abcd.as_ref()).unwrap();
    assert_eq!((aa, bb, cc, dd), (a, b, c, d));
    let (aa, bb, cc, dd, ee) =
      <(i32, i32, i32, i32, i32)>::from_glyph(abcde.as_ref()).unwrap();
    assert_eq!((aa, bb, cc, dd, ee), (a, b, c, d, e));
    let (aa, bb, cc, dd, ee, ff) =
      <(i32, i32, i32, i32, i32, i32)>::from_glyph(abcdef.as_ref()).unwrap();
    assert_eq!((aa, bb, cc, dd, ee, ff), (a, b, c, d, e, f));

    let tg = TupleGlyph::from_glyph(abcdef).unwrap();

    // Test `TupleGlyph::get()`
    assert_eq!(i32::from_glyph(tg.get(0).unwrap()).unwrap(), 8);
    assert_eq!(i32::from_glyph(tg.get(1).unwrap()).unwrap(), 6);
    assert_eq!(i32::from_glyph(tg.get(2).unwrap()).unwrap(), 7);
    assert_eq!(i32::from_glyph(tg.get(3).unwrap()).unwrap(), 5);
    assert_eq!(i32::from_glyph(tg.get(4).unwrap()).unwrap(), 3);
    assert_eq!(i32::from_glyph(tg.get(5).unwrap()).unwrap(), 0);
    assert!(tg.get(6).is_err());

    let mut sum = 0;
    for glyph in tg.iter() {
      sum += i32::from_glyph(glyph).unwrap();
    }
    assert_eq!(sum, 8 + 6 + 7 + 5 + 3);
  }
}
