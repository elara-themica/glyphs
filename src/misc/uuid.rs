use crate::{
  zerocopy::{bounds_check, HasZeroCopyID, ZeroCopy, ZeroCopyTypeID},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphSorting, GlyphType, ParsedGlyph, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
};
use std::cmp::Ordering;
use uuid::Uuid;

impl ToGlyph for Uuid {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new(GlyphType::UUID, size_of::<Uuid>())?
      .bbwr(target, cursor)?;
    u8::bbwrs(&self.as_bytes()[..], target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>() + size_of::<Uuid>()
  }
}

unsafe impl ZeroCopy for Uuid {}

impl HasZeroCopyID for Uuid {
  const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::UUID;
}

impl<T> FromGlyph<T> for Uuid
where
  T: Glyph,
{
  fn from_glyph(source: T) -> Result<Self, FromGlyphErr<T>> {
    if let Err(err) = source.confirm_type(GlyphType::UUID) {
      return Err(err.into_fge(source));
    }
    let content = source.content_padded();
    let cursor = &mut 0;
    let bytes = match u8::bbrda::<[u8], 16>(content, cursor) {
      Ok(bytes) => bytes,
      Err(err) => return Err(err.into_fge(source)),
    };
    Ok(Uuid::from_bytes(bytes))
  }
}

impl<'a> FromGlyph<ParsedGlyph<'a>> for &'a Uuid {
  fn from_glyph(
    source: ParsedGlyph<'a>,
  ) -> Result<Self, FromGlyphErr<ParsedGlyph<'a>>> {
    if let Err(err) = source.confirm_type(GlyphType::UUID) {
      return Err(err.into_fge(source));
    }
    let content = source.content_parsed();
    if let Err(err) = bounds_check(content, size_of::<Uuid>()) {
      return Err(err.into_fge(source));
    }
    // SAFETY: We just did a bounds check, and Uuid is guaranteed to have the
    // same ABI as [u8; 16]
    unsafe { Ok(&*(content.as_ptr() as *const Uuid)) }
  }
}

gen_prim_slice_to_glyph!(Uuid);
gen_prim_slice_from_glyph_parsed!(Uuid);

/// Glyph containing a UUID.
pub struct UuidGlyph<T>(T)
where
  T: Glyph;

impl<T> UuidGlyph<T>
where
  T: Glyph,
{
  /// Returns a reference to the UUID contained in the glyph.
  pub fn get(&self) -> &Uuid {
    // SAFETY: Bounds check was performed upon creation, and Uuid has the same
    // UBI as [u8; 16].  See `from_glyph()`.
    unsafe { &*(self.0.content_padded().as_ptr() as *const Uuid) }
  }
}

impl<T> Debug for UuidGlyph<T>
where
  T: Glyph,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "UuidGlyph({:?})", self.get())
  }
}

impl<T> FromGlyph<T> for UuidGlyph<T>
where
  T: Glyph,
{
  fn from_glyph(source: T) -> Result<Self, FromGlyphErr<T>> {
    if let Err(err) = source.confirm_type(GlyphType::UUID) {
      return Err(err.into_fge(source));
    }
    if let Err(err) = bounds_check(source.content_padded(), size_of::<Uuid>()) {
      return Err(err.into_fge(source));
    }
    Ok(UuidGlyph(source))
  }
}

impl<G: Glyph> PartialEq for UuidGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for UuidGlyph<G> {}

impl<G: Glyph> PartialOrd for UuidGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for UuidGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Glyph> EncodedGlyph<G> for UuidGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      _ => self.0.content().cmp(other.0.content()),
    }
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::{collections::BasicVecGlyph, glyph_new};
  use alloc::vec::Vec;
  use std::dbg;

  #[test]
  fn codec_uuid() -> Result<(), GlyphErr> {
    // Scalar tests
    let uuid = Uuid::new_v4();
    dbg!(&uuid);
    let glyph = glyph_new(&uuid)?;
    dbg!(&glyph);
    let uuid_ref = <&Uuid>::from_glyph(glyph.borrow())?;
    assert_eq!(uuid, *uuid_ref);
    let new_uuid = Uuid::from_glyph(glyph.borrow())?;
    assert_eq!(uuid, new_uuid);

    let uuid_glyph = UuidGlyph::from_glyph(glyph.borrow())?;
    dbg!(&uuid_glyph);
    assert_eq!(uuid_glyph.get(), &uuid);

    // Vector tests
    let mut uuids = Vec::new();
    for _ in 0..4 {
      uuids.push(Uuid::new_v4());
    }
    dbg!(&uuids);
    let glyph = glyph_new(&uuids[..])?;
    dbg!(&glyph);
    let uuids_decoded = <&[Uuid]>::from_glyph(glyph.borrow())?;
    assert_eq!(uuids_decoded, &uuids);
    let vec_uuid_glyph = BasicVecGlyph::<_>::from_glyph(glyph.borrow())?;
    assert_eq!(vec_uuid_glyph.get::<Uuid>()?, &uuids[..]);
    let uuids_parsed = vec_uuid_glyph.get_parsed::<Uuid>()?;
    drop(vec_uuid_glyph);
    assert_eq!(uuids_parsed, &uuids[..]);
    drop(glyph);
    // Compiler error, now referencing lifetime from a dropped object.
    // dbg!(uuids_parsed);

    Ok(())
  }
}
