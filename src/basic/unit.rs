use crate::{
  zerocopy::ZeroCopy, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  ToGlyph,
};
use core::mem::transmute;

/// Glyph for Unit Types
///
/// A Glyph that represents several different unit types, i.e., types with no
/// further information, e.g., [`()`] or [`Option::None`].  For the list of
/// known unit types, see `enum` [`UnitTypes`] .
#[derive(Copy, Clone, Debug)]
pub struct UnitG<G: Glyph>(G, UnitTypes);

impl<G: Glyph> UnitG<G> {
  /// Returns the specific unit type represented by the glyph.
  pub fn type_id(&self) -> &UnitTypes {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for UnitG<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::Unit)?;
    if glyph.header().is_short() {
      let type_id = u32::from_le_bytes(*glyph.header().short_content());
      // SAFETY: repr(u32)
      let type_id: UnitTypes = unsafe { transmute::<_, _>(type_id) };
      Ok(UnitG(glyph, type_id))
    } else {
      err!(debug, Err(GlyphErr::UnitLength(glyph.content().len())))
    }
  }
}

/// A list of unit types that can be represented by a unit glyph ([`UnitG`]).
///
/// See the Wikipedia article [Unit Types](https://en.wikipedia.org/wiki/Unit_type)
/// for more information.
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
#[repr(u32)]
#[non_exhaustive]
pub enum UnitTypes {
  /// Represents the absence of something, e.g., [`Option::None`].
  Nothing = 0x0000_0000,
  /// Represents some information that is unknown
  Unknown = 0x0000_0001,
  /// Represents some information that has been redacted
  Redacted = 0x0000_0002,
}

impl ToGlyph for UnitTypes {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // SAFETY: repr(u32)
    let type_id: u32 = unsafe { transmute::<_, _>(*self) };
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
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::Unit)?;
    let content = glyph.short_content();
    let type_id = u32::from_le_bytes(*content);
    // SAFETY: repr(u32)
    let type_id: UnitTypes = unsafe { transmute::<_, _>(type_id) };
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
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    let ug = UnitTypes::from_glyph(glyph)?;
    if ug.eq(&UnitTypes::Nothing) {
      Ok(())
    } else {
      err!(
        debug,
        Err(GlyphErr::UnitTypeMismatch {
          expected: UnitTypes::Nothing,
          observed: ug,
        })
      )
    }
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
    let ug = UnitG::from_glyph(nothing_glyph.borrow()).unwrap();
    assert_eq!(ug.type_id(), &UnitTypes::Nothing);
  }
}
