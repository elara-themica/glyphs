//! Numbers, strings, boolean, nothing, option, etc...
#[allow(unused_imports)]
use crate::{
  zerocopy::{F32, F64, I128, I16, I32, I64, U128, U16, U32, U64},
  FromGlyph, Glyph, GlyphErr, GlyphType, ToGlyph,
};
#[allow(unused_imports)]
use core::str::from_utf8;
use std::ops::Deref;

mod bool;
pub use bool::*;

mod lang;
pub use lang::*;

mod numeric;
pub use numeric::*;

mod unit;
pub use unit::*;

mod zc;
use crate::DecodeErr;
pub use zc::*;

impl<T> ToGlyph for Option<T>
where
  T: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match self {
      None => ().glyph_encode(target, cursor),
      Some(src) => src.glyph_encode(target, cursor),
    }
  }

  fn glyph_len(&self) -> usize {
    match self {
      None => ().glyph_len(),
      Some(src) => src.glyph_len(),
    }
  }
}

impl<B, T> FromGlyph<B> for Option<T>
where
  B: Deref<Target = Glyph>,
  T: FromGlyph<B>,
  GlyphErr: From<T::Error>,
{
  type Error = GlyphErr;

  fn from_glyph(source: B) -> Result<Self, DecodeErr<B, Self::Error>> {
    let type_id = source.header().glyph_type();
    if type_id == GlyphType::Unit {
      let unit = match UnitGlyph::from_glyph(source.deref()) {
        Ok(unit) => unit,
        Err(err) => {
          let (_glyph, err) = err.into_parts();
          return Err(DecodeErr::new(source, err));
        },
      };
      let unit_type_id = *unit.type_id();
      if unit_type_id.eq(&UnitType::Nothing) {
        Ok(None)
      } else {
        Err(err!(
          debug,
          DecodeErr::new(source, GlyphErr::UnexpectedUnitType(unit_type_id))
        ))
      }
    } else {
      match T::from_glyph(source) {
        Ok(val) => Ok(Some(val)),
        Err(err) => Err(err.map_err(|err| GlyphErr::from(err))),
      }
    }
  }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    util::test::{simple_codec_slice_test, simple_codec_test},
    FromGlyph, Glyph,
  };
  use alloc::string::String;
  use core::ops::Deref;

  #[test]
  fn codec_basic() {
    //=== Simple Scalar Values ===/
    simple_codec_test(());
    simple_codec_test(Option::<u32>::None);
    simple_codec_test(Option::<u32>::Some(0xDEAD_BEEF));
    simple_codec_test(0xDEADBEEFu32);
    simple_codec_test(0xF00DDEADBEEFF00Du64);
    simple_codec_test(0x0102030405060708090A0B0C0D0E0Fu128);
    simple_codec_test(-32i32);
    simple_codec_test(-64i64);
    simple_codec_test(-128i128);
    simple_codec_test('🦋');

    //=== Simple Slices ===/
    simple_codec_slice_test::<3, u8, u8>(42u8);
    simple_codec_slice_test::<3, u16, U16>(0xF00D);
    simple_codec_slice_test::<3, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<3, u64, U64>(0xF00DDEADBEEFF00D);
    simple_codec_slice_test::<3, u128, U128>(123);
    simple_codec_slice_test::<3, i8, i8>(-1);
    simple_codec_slice_test::<3, i16, I16>(-1);
    simple_codec_slice_test::<3, i32, I32>(-1);
    simple_codec_slice_test::<3, i64, I64>(-1);
    simple_codec_slice_test::<3, i128, I128>(-1234);
    simple_codec_slice_test::<3, f32, F32>(core::f32::consts::E);
    simple_codec_slice_test::<3, f64, F64>(core::f64::consts::E);
    // No basic slice for `char`, as it's not safely zero-copy.

    //=== Vary Slice Lengths ===/
    simple_codec_slice_test::<0, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<1, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<2, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<3, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<7, u32, U32>(0xDEAD_BEEF);
    simple_codec_slice_test::<8, u32, U32>(0xDEAD_BEEF);

    //=== Strings ===/
    let text = "hunter2";
    let glyph = Glyph::new(text).unwrap();
    let read_str = <&str>::from_glyph(glyph.as_ref()).unwrap();
    assert_eq!(read_str, text);
    let read_string = String::from_glyph(glyph.as_ref()).unwrap();
    assert_eq!(read_string.as_str(), text);
    let str_glyph = StringGlyph::from_glyph(glyph.as_ref()).unwrap();
    assert_eq!(str_glyph.deref(), text);

    //=== Vary String Lengths ===/
    let mut text = String::new();
    for _i in 0..64 {
      let glyph = Glyph::new(&text).unwrap();
      let read_str = <&str>::from_glyph(glyph.as_ref()).unwrap();
      assert_eq!(read_str, text);
      text.push('a');
    }

    //=== Unit Type ===//
    let nothing_glyph = Glyph::new(&UnitType::Nothing).unwrap();
    let ut = UnitType::from_glyph(nothing_glyph.as_ref()).unwrap();
    assert_eq!(ut, UnitType::Nothing);
    let ug = UnitGlyph::from_glyph(nothing_glyph.as_ref()).unwrap();
    assert_eq!(ug.type_id(), &UnitType::Nothing);
    // Resulting glyphs from using the `()` type directly should be the same as
    // explicitly using `UnitType::Nothing`.
    let from_unit_type = Glyph::new(()).unwrap();
    assert_eq!(from_unit_type.as_ref(), nothing_glyph.as_ref());
  }
}
