use crate::{
  zerocopy::{ZeroCopy, U32},
  EncodedGlyph, FromGlyph, Glyph, GlyphDecodeErr, GlyphErr, GlyphHeader,
  GlyphType, ToGlyph,
};
use core::{fmt::Debug, mem::transmute};
use std::{cmp::Ordering, ops::Deref};

/// Glyph for Unit Types
///
/// A Glyph that represents several different unit types, i.e., types with no
/// further information, e.g., [`()`] or [`Option::None`].  For the list of
/// known unit types, see `enum` [`UnitType`] .
#[derive(Copy, Clone)]
pub struct UnitGlyph<G: Deref<Target = Glyph>>(G, UnitType);

impl<G: Deref<Target = Glyph>> UnitGlyph<G> {
  /// Returns the specific unit type represented by the glyph.
  pub fn type_id(&self) -> &UnitType {
    &self.1
  }
}

impl<G: Deref<Target = Glyph>> Debug for UnitGlyph<G> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "UnitGlyph({:?})", self.type_id())?;
    Ok(())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for UnitGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

impl<G: Deref<Target = Glyph>> Eq for UnitGlyph<G> {}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for UnitGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    match glyph.header().confirm_type(GlyphType::Unit) {
      Ok(()) => {
        if glyph.header().is_short() {
          let type_id = u32::from_le_bytes(*glyph.header().short_content());
          let type_id = UnitType::from(type_id);
          Ok(UnitGlyph(glyph, type_id))
        } else {
          let glyph_len = glyph.as_ref().len();
          Err(GlyphDecodeErr::new(glyph, GlyphErr::UnitLength(glyph_len)))
        }
      },
      Err(err) => Err(GlyphDecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Ord for UnitGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.1.cmp(&other.1)
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for UnitGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for UnitGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// A list of unit types that can be represented by a unit glyph ([`UnitGlyph`]).
///
/// See the Wikipedia article [Unit Types](https://en.wikipedia.org/wiki/Unit_type)
/// for more information.
///
// SAFETY: For safe conversions from u32 values, this list must be (1)
//         contiguous and (2) end with `UnknownType` as the highest value.
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
#[repr(u32)]
#[non_exhaustive]
#[allow(missing_docs)]
pub enum UnitType {
  Nothing = 0x0000_0000,
  Unknown = 0x0000_0001,
  Redacted = 0x0000_0002,
  UnknownType = 0x0000_0003,
}

impl From<u32> for UnitType {
  fn from(value: u32) -> Self {
    unsafe {
      if value > UnitType::UnknownType as u32 {
        UnitType::UnknownType
      } else {
        transmute::<u32, UnitType>(value)
      }
    }
  }
}

impl From<U32> for UnitType {
  fn from(value: U32) -> Self {
    value.get().into()
  }
}

impl From<UnitType> for u32 {
  fn from(value: UnitType) -> Self {
    value as u32 // If no compile, use transmute--should be safe.
  }
}

impl From<UnitType> for U32 {
  fn from(value: UnitType) -> Self {
    U32::from(value as u32)
  }
}

impl<G> FromGlyph<G> for UnitType
where
  G: Deref<Target = Glyph>,
{
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    if let Err(err) = glyph.header().confirm_type(GlyphType::Unit) {
      return Err(GlyphDecodeErr::new(glyph, err));
    }
    let content = glyph.header().short_content();
    let type_id = u32::from_le_bytes(*content);
    let type_id = UnitType::from(type_id);
    Ok(type_id)
  }
}

impl ToGlyph for UnitType {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let type_id = u32::from(*self);
    let bytes = type_id.to_le_bytes();
    GlyphHeader::new_short(GlyphType::Unit, bytes).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl<G> FromGlyph<G> for ()
where
  G: Deref<Target = Glyph>,
{
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    let ug = match UnitType::from_glyph(glyph.deref()) {
      Ok(unit_type) => unit_type,
      Err(err) => {
        let (_glyph, err) = err.into_parts();
        return Err(GlyphDecodeErr::new(glyph, err));
      },
    };
    if ug.eq(&UnitType::Nothing) {
      Ok(())
    } else {
      err!(
        debug,
        Err(GlyphDecodeErr::new(
          glyph,
          GlyphErr::UnitTypeMismatch {
            expected: UnitType::Nothing,
            observed: ug,
          }
        ))
      )
    }
  }
}

impl ToGlyph for () {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    UnitType::Nothing.glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    UnitType::Nothing.glyph_len()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn codec_unit() {
    let nothing_glyph = Glyph::new(&UnitType::Nothing).unwrap();
    std::dbg!(&nothing_glyph);
    let ut = UnitType::from_glyph(nothing_glyph.as_ref()).unwrap();
    assert_eq!(ut, UnitType::Nothing);
    let ug = UnitGlyph::from_glyph(nothing_glyph.as_ref()).unwrap();
    assert_eq!(ug.type_id(), &UnitType::Nothing);
  }
}
