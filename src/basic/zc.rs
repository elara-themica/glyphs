use crate::{
  zerocopy::{bounds_check, ZeroCopyGlyph},
  DecodeErr, EncodedGlyph, FromGlyph, Glyph, GlyphErr,
};
use core::fmt::{Debug, Formatter};
use std::{cmp::Ordering, marker::PhantomData, ops::Deref};

/// A single instance of a basic zero-copy type, e.g., a [`U32`].
///
/// The type is generic over the type of glyph `G`, allowing it to be
/// constructed from borrowed or owned data, and over the corresponding type
/// `T`, which must implement [`ZeroCopyGlyph`].  This requires that the type
/// be readable directly from a string of bytes (i.e., is [`ZeroCopy`]) as well
/// as providing an associated [`GlyphType`].
///
/// This type can only be constructed via the [`FromGlyph`] trait, which will
/// check that (1) type ID of the source glyph matches that of the target type,
/// and (2) will perform a bounds check to ensure the glyph is large enough to
/// contain an instance of `T`.
///
/// Types with a size of <= 4 bytes will be written as short glyphs and read
/// from the glyph header.
///
// TODO: Write doc example.
pub struct BasicGlyph<G: Deref<Target = Glyph>, T: ZeroCopyGlyph>(
  G,
  PhantomData<T>,
);

impl<'a, T: ZeroCopyGlyph> BasicGlyph<&'a Glyph, T> {
  /// Returns a reference to the target type from the underlying buffer (i.e.,
  /// not also this `BasicGlyph`.
  pub fn get_parsed(&self) -> &'a T {
    // SAFETY: We already did the bounds check in `FromGlyph`.
    unsafe {
      let buf = if size_of::<T>() > 4 {
        self.0.content_padded()
      } else {
        &self.0.header().short_content()[..]
      };
      T::bbrf_u(buf, &mut 0)
    }
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> Debug for BasicGlyph<G, T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    Debug::fmt(self.deref(), f)
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> Deref for BasicGlyph<G, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    // SAFETY: We already did the bounds check in `FromGlyph`.
    unsafe {
      let buf = if size_of::<T>() > 4 {
        self.0.content_padded()
      } else {
        &self.0.header().short_content()[..]
      };
      T::bbrf_u(buf, &mut 0)
    }
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> EncodedGlyph<G>
  for BasicGlyph<G, T>
{
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> Eq for BasicGlyph<G, T> {}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> FromGlyph<G>
  for BasicGlyph<G, T>
{
  type Error = GlyphErr;

  fn from_glyph(glyph: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    if let Err(err) = glyph.header().confirm_type(T::GLYPH_TYPE_ID) {
      return Err(DecodeErr::new(glyph, err));
    }

    if size_of::<T>() > 4 {
      if let Err(err) = bounds_check(glyph.content_padded(), size_of::<T>()) {
        return Err(DecodeErr::new(glyph, err.into()));
      }

      Ok(Self(glyph, PhantomData::default()))
    } else {
      Ok(Self(glyph, PhantomData::default()))
    }
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> Ord for BasicGlyph<G, T> {
  fn cmp(&self, other: &Self) -> Ordering {
    self
      .glyph()
      .header()
      .glyph_type()
      .cmp(&other.glyph().header().glyph_type())
      .then_with(|| self.deref().cmp(other.deref()))
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> PartialEq
  for BasicGlyph<G, T>
{
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>, T: ZeroCopyGlyph> PartialOrd
  for BasicGlyph<G, T>
{
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
