use crate::{
  zerocopy::{ZeroCopy, F32, F64, I128, I16, I32, I64, U128, U16, U32, U64},
  FromGlyph, Glyph, GlyphErr,
  GlyphType::{Float, SignedInt, UnsignedInt},
};
use std::ops::Deref;

/// Signed integers
///
/// 32-, 64-, and 128-bit versions are supported.
///
///
///
/// ```
/// use glyphs::{glyph_new, FromGlyph};
///
/// // 32-bit encoding and decoding
/// let g = glyph_new(42i32).unwrap();
/// assert_eq!(g.as_ref().len(), 8);
/// let decoded = i32::from_glyph(g).unwrap();
/// assert_eq!(decoded, 42i32);
///
///
///
/// ```
#[derive(Copy, Clone, Debug)]
pub struct IntG<G: Glyph>(G, i128);

impl<G: Glyph> IntG<G> {
  /// Returns the value in the glyph.
  pub fn get(&self) -> &i128 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for IntG<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(SignedInt)?;
    let val = if glyph.header().is_short() {
      i32::from_le_bytes(*glyph.header().short_content()) as i128
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<I128>() {
          I128::bbrf_u(buf, &mut 0).get()
        } else if buf.len() >= size_of::<I64>() {
          I64::bbrf_u(buf, &mut 0).get() as i128
        } else {
          0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for IntG<G> {
  type Target = i128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<IntG<G>> for i128 {
  fn from(value: IntG<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<IntG<G>> for i64 {
  type Error = GlyphErr;

  fn try_from(value: IntG<G>) -> Result<Self, Self::Error> {
    let value =
      i64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntG<G>> for i32 {
  type Error = GlyphErr;

  fn try_from(value: IntG<G>) -> Result<Self, Self::Error> {
    let value =
      i32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntG<G>> for i16 {
  type Error = GlyphErr;

  fn try_from(value: IntG<G>) -> Result<Self, Self::Error> {
    let value =
      i16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntG<G>> for i8 {
  type Error = GlyphErr;

  fn try_from(value: IntG<G>) -> Result<Self, Self::Error> {
    let value =
      i8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

/// A glyph containing an unsigned integer.
///
/// Currently, values up to a `u128` are supported, which is what will be
/// returned by [`Deref`].  However, note that there are [`TryFrom`]
/// implementations for the smaller unsigned integer types.
pub struct UIntG<G: Glyph>(G, u128);

impl<G: Glyph> UIntG<G> {
  /// Gets the value in the glyph.
  pub fn get(&self) -> &u128 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for UIntG<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(UnsignedInt)?;
    let val = if glyph.header().is_short() {
      u32::from_le_bytes(*glyph.header().short_content()) as u128
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<U128>() {
          U128::bbrf_u(buf, &mut 0).get()
        } else if buf.len() >= size_of::<U64>() {
          U64::bbrf_u(buf, &mut 0).get() as u128
        } else {
          0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for UIntG<G> {
  type Target = u128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<UIntG<G>> for u128 {
  fn from(value: UIntG<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<UIntG<G>> for u64 {
  type Error = GlyphErr;

  fn try_from(value: UIntG<G>) -> Result<Self, Self::Error> {
    let value =
      u64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntG<G>> for u32 {
  type Error = GlyphErr;

  fn try_from(value: UIntG<G>) -> Result<Self, Self::Error> {
    let value =
      u32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntG<G>> for u16 {
  type Error = GlyphErr;

  fn try_from(value: UIntG<G>) -> Result<Self, Self::Error> {
    let value =
      u16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntG<G>> for u8 {
  type Error = GlyphErr;

  fn try_from(value: UIntG<G>) -> Result<Self, Self::Error> {
    let value =
      u8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

/// A glyph containing a floating point number.
///
/// Currently, only `f32` and `f64` are supported, the latter of which is
/// returned by [`Deref`].  However, note that there is also a direct [`From`]
/// implementation from this type into a `f32`.
pub struct FloatG<G: Glyph>(G, f64);

impl<G: Glyph> FloatG<G> {
  /// Returns the value in the glyph.
  pub fn get(&self) -> &f64 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for FloatG<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(Float)?;
    let val = if glyph.header().is_short() {
      f32::from_le_bytes(*glyph.header().short_content()) as f64
    } else {
      let buf = glyph.content_padded();
      // SAFETY: Bounds checks are redundant with switching on length
      unsafe {
        if buf.len() >= size_of::<F64>() {
          F64::bbrf_u(buf, &mut 0).get()
        } else {
          0.0
        }
      }
    };
    Ok(Self(glyph, val))
  }
}

impl<G: Glyph> Deref for FloatG<G> {
  type Target = f64;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<FloatG<G>> for f32 {
  fn from(value: FloatG<G>) -> Self {
    value.1 as f32
  }
}

gen_prim_to_glyph!(u8, UnsignedInt, short, |src: &u8| {
  u32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(u16, UnsignedInt, short, |src: &u16| {
  u32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(u32, UnsignedInt, short, |src: &u32| { src.to_le_bytes() });
gen_prim_to_glyph!(u64, UnsignedInt, conv, U64, |src: &u64| {
  U64::from(*src)
});
gen_prim_to_glyph!(u128, UnsignedInt, conv, U128, |src: &u128| {
  U128::from(*src)
});
gen_prim_to_glyph!(i8, SignedInt, short, |src: &i8| {
  i32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(i16, SignedInt, short, |src: &i16| {
  i32::from(*src).to_le_bytes()
});
gen_prim_to_glyph!(i32, SignedInt, short, |src: &i32| { src.to_le_bytes() });
gen_prim_to_glyph!(i64, SignedInt, conv, I64, |src: &i64| { I64::from(*src) });
gen_prim_to_glyph!(i128, SignedInt, conv, I128, |src: &i128| {
  I128::from(*src)
});
gen_prim_to_glyph!(f32, Float, short, |src: &f32| { src.to_le_bytes() });
gen_prim_to_glyph!(f64, Float, conv, F64, |src: &f64| { F64::from(*src) });
gen_prim_to_glyph!(U16, UnsignedInt, short, |src: &U16| {
  u32::from(src.get()).to_le_bytes()
});
gen_prim_to_glyph!(U32, UnsignedInt, short, |src: &U32| *src.bytes());
gen_prim_to_glyph!(U64, UnsignedInt);
gen_prim_to_glyph!(U128, UnsignedInt);
gen_prim_to_glyph!(I16, SignedInt, short, |src: &I16| {
  i32::from(src.get()).to_le_bytes()
});
gen_prim_to_glyph!(I32, SignedInt, short, |src: &I32| *src.bytes());
gen_prim_to_glyph!(I64, SignedInt);
gen_prim_to_glyph!(I128, SignedInt);
gen_prim_to_glyph!(F32, Float, short, |src: &F32| { *src.bytes() });
gen_prim_to_glyph!(F64, Float);

gen_prim_slice_to_glyph!(u8);
gen_prim_slice_to_glyph!(u16, conv, U16, |src: &u16| U16::from(*src));
gen_prim_slice_to_glyph!(u32, conv, U32, |src: &u32| U32::from(*src));
gen_prim_slice_to_glyph!(u64, conv, U64, |src: &u64| U64::from(*src));
gen_prim_slice_to_glyph!(u128, conv, U128, |src: &u128| U128::from(*src));
gen_prim_slice_to_glyph!(i8);
gen_prim_slice_to_glyph!(i16, conv, I16, |src: &i16| I16::from(*src));
gen_prim_slice_to_glyph!(i32, conv, I32, |src: &i32| I32::from(*src));
gen_prim_slice_to_glyph!(i64, conv, I64, |src: &i64| I64::from(*src));
gen_prim_slice_to_glyph!(i128, conv, I128, |src: &i128| I128::from(*src));
gen_prim_slice_to_glyph!(f32, conv, F32, |src: &f32| F32::from(*src));
gen_prim_slice_to_glyph!(f64, conv, F64, |src: &f64| F64::from(*src));
gen_prim_slice_to_glyph!(U16);
gen_prim_slice_to_glyph!(U32);
gen_prim_slice_to_glyph!(U64);
gen_prim_slice_to_glyph!(U128);
gen_prim_slice_to_glyph!(I16);
gen_prim_slice_to_glyph!(I32);
gen_prim_slice_to_glyph!(I64);
gen_prim_slice_to_glyph!(I128);
gen_prim_slice_to_glyph!(F32);
gen_prim_slice_to_glyph!(F64);

gen_prim_from_glyph!(u8, try_conv_glyph, UIntG, |gl: UIntG<G>| {
  u8::try_from(*gl)
});
gen_prim_from_glyph!(u16, try_conv_glyph, UIntG, |gl: UIntG<G>| {
  u16::try_from(*gl)
});
gen_prim_from_glyph!(u32, try_conv_glyph, UIntG, |gl: UIntG<G>| {
  u32::try_from(*gl)
});
gen_prim_from_glyph!(u64, try_conv_glyph, UIntG, |gl: UIntG<G>| {
  u64::try_from(*gl)
});
gen_prim_from_glyph!(u128, try_conv_glyph, UIntG, |gl: UIntG<G>| {
  u128::try_from(*gl)
});
gen_prim_from_glyph!(i8, try_conv_glyph, IntG, |gl: IntG<G>| {
  i8::try_from(*gl)
});
gen_prim_from_glyph!(i16, try_conv_glyph, IntG, |gl: IntG<G>| {
  i16::try_from(*gl)
});
gen_prim_from_glyph!(i32, try_conv_glyph, IntG, |gl: IntG<G>| {
  i32::try_from(*gl)
});
gen_prim_from_glyph!(i64, try_conv_glyph, IntG, |gl: IntG<G>| {
  i64::try_from(*gl)
});
gen_prim_from_glyph!(i128, try_conv_glyph, IntG, |gl: IntG<G>| {
  i128::try_from(*gl)
});
gen_prim_from_glyph!(f32, conv_glyph, FloatG, |gl: FloatG<G>| { (*gl) as f32 });
gen_prim_from_glyph!(f64, conv_glyph, FloatG, |gl: FloatG<G>| { *gl });
gen_prim_from_glyph!(U32, conv, u32, |val| { U32::from(val) });
gen_prim_from_glyph!(U64, conv, u64, |val| { U64::from(val) });
gen_prim_from_glyph!(U128, conv, u128, |val| { U128::from(val) });
gen_prim_from_glyph!(I32, conv, i32, |val| { I32::from(val) });
gen_prim_from_glyph!(I64, conv, i64, |val| { I64::from(val) });
gen_prim_from_glyph!(I128, conv, i128, |val| { I128::from(val) });
gen_prim_from_glyph!(F32, conv, f32, |val| { F32::from(val) });
gen_prim_from_glyph!(F64, conv, f64, |val| { F64::from(val) });

gen_prim_slice_from_glyph_parsed!(u8);
gen_prim_slice_from_glyph_parsed!(U16, le_native, u16);
gen_prim_slice_from_glyph_parsed!(U32, le_native, u32);
gen_prim_slice_from_glyph_parsed!(U64, le_native, u64);
gen_prim_slice_from_glyph_parsed!(U128);
gen_prim_slice_from_glyph_parsed!(i8);
gen_prim_slice_from_glyph_parsed!(I16, le_native, i16);
gen_prim_slice_from_glyph_parsed!(I32, le_native, i32);
gen_prim_slice_from_glyph_parsed!(I64, le_native, i64);
gen_prim_slice_from_glyph_parsed!(I128);
gen_prim_slice_from_glyph_parsed!(F32, le_native, f32);
gen_prim_slice_from_glyph_parsed!(F64, le_native, f64);
