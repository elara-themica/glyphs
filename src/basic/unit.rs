use crate::{
  zerocopy::{ZeroCopy, U32},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ParsedGlyph, ToGlyph,
};
use core::mem::transmute;
use std::cmp::Ordering;

/// Glyph for Unit Types
///
/// A Glyph that represents several different unit types, i.e., types with no
/// further information, e.g., [`()`] or [`Option::None`].  For the list of
/// known unit types, see `enum` [`UnitTypes`] .
#[derive(Copy, Clone)]
pub struct UnitGlyph<G: Glyph>(G, UnitTypes);

impl<G: Glyph> UnitGlyph<G> {
  /// Returns the specific unit type represented by the glyph.
  pub fn type_id(&self) -> &UnitTypes {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for UnitGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(GlyphType::Unit) {
      return Err(err.into_fge(glyph));
    }
    if glyph.header().is_short() {
      let type_id = u32::from_le_bytes(*glyph.header().short_content());
      let type_id = UnitTypes::from(type_id);
      Ok(UnitGlyph(glyph, type_id))
    } else {
      err!(
        debug,
        Err(GlyphErr::UnitLength(glyph.content().len()).into_fge(glyph))
      )
    }
  }
}

impl<G: Glyph> core::fmt::Debug for UnitGlyph<G> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "UnitGlyph({:?})", self.type_id())?;
    Ok(())
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
pub enum UnitTypes {
  Nothing = 0x0000_0000,
  Unknown = 0x0000_0001,
  Redacted = 0x0000_0002,
  UnknownType = 0x0000_0003,
}

impl From<u32> for UnitTypes {
  fn from(value: u32) -> Self {
    unsafe {
      if value > UnitTypes::UnknownType as u32 {
        UnitTypes::UnknownType
      } else {
        transmute::<u32, UnitTypes>(value)
      }
    }
  }
}

impl From<U32> for UnitTypes {
  fn from(value: U32) -> Self {
    value.get().into()
  }
}

impl From<UnitTypes> for u32 {
  fn from(value: UnitTypes) -> Self {
    value as u32 // If no compile, use transmute--should be safe.
  }
}

impl From<UnitTypes> for U32 {
  fn from(value: UnitTypes) -> Self {
    U32::from(value as u32)
  }
}

impl ToGlyph for UnitTypes {
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

impl<G> FromGlyph<G> for UnitTypes
where
  G: Glyph,
{
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(GlyphType::Unit) {
      return Err(err.into_fge(glyph));
    }
    let content = glyph.short_content();
    let type_id = u32::from_le_bytes(*content);
    let type_id = UnitTypes::from(type_id);
    Ok(type_id)
  }
}

impl ToGlyph for () {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    UnitTypes::Nothing.glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    UnitTypes::Nothing.glyph_len()
  }
}

impl<G> FromGlyph<G> for ()
where
  G: Glyph,
{
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let ug = match UnitTypes::from_glyph(glyph.borrow()) {
      Ok(unit_type) => unit_type,
      Err(err) => {
        let (_glyph, err) = err.into_parts();
        return Err(err.into_fge(glyph));
      },
    };
    if ug.eq(&UnitTypes::Nothing) {
      Ok(())
    } else {
      err!(
        debug,
        Err(
          GlyphErr::UnitTypeMismatch {
            expected: UnitTypes::Nothing,
            observed: ug,
          }
          .into_fge(glyph)
        )
      )
    }
  }
}

impl<G: Glyph> PartialEq for UnitGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for UnitGlyph<G> {}

impl<G: Glyph> PartialOrd for UnitGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for UnitGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.1.cmp(&other.1)
  }
}

impl<G: Glyph> EncodedGlyph<G> for UnitGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::glyph_new;

  #[test]
  fn codec_unit() {
    let nothing_glyph = glyph_new(&UnitTypes::Nothing).unwrap();
    std::dbg!(&nothing_glyph);
    let ut = UnitTypes::from_glyph(nothing_glyph.borrow()).unwrap();
    assert_eq!(ut, UnitTypes::Nothing);
    let ug = UnitGlyph::from_glyph(nothing_glyph.borrow()).unwrap();
    assert_eq!(ug.type_id(), &UnitTypes::Nothing);
  }
}
