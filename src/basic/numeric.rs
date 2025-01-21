use crate::{
  zerocopy::{ZeroCopy, F32, F64, I128, I16, I32, I64, U128, U16, U32, U64},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr,
  GlyphType::{Float, SignedInt, UnsignedInt},
  ParsedGlyph,
};
use core::fmt::{Debug, Formatter};
use std::{cmp::Ordering, ops::Deref};

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
pub struct IntGlyph<G: Glyph>(G, i128);

impl<G: Glyph> IntGlyph<G> {
  /// Returns the value in the glyph.
  pub fn get(&self) -> &i128 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for IntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(SignedInt) {
      return Err(err.into_fge(glyph));
    }
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

impl<G: Glyph> Deref for IntGlyph<G> {
  type Target = i128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<IntGlyph<G>> for i128 {
  fn from(value: IntGlyph<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i64 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i32 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i16 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<IntGlyph<G>> for i8 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      i8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> PartialEq for IntGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.1 == other.1
  }
}

impl<G: Glyph> Eq for IntGlyph<G> {}

impl<G: Glyph> PartialOrd for IntGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for IntGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.1.cmp(&other.1)
  }
}

impl<G: Glyph> EncodedGlyph<G> for IntGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

/// A glyph containing an unsigned integer.
///
/// Currently, values up to a `u128` are supported, which is what will be
/// returned by [`Deref`].  However, note that there are [`TryFrom`]
/// implementations for the smaller unsigned integer types.
pub struct UIntGlyph<G: Glyph>(G, u128);

impl<G: Glyph> UIntGlyph<G> {
  /// Gets the value in the glyph.
  pub fn get(&self) -> &u128 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for UIntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(UnsignedInt) {
      return Err(err.into_fge(glyph));
    }
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

impl<G: Glyph> Deref for UIntGlyph<G> {
  type Target = u128;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<UIntGlyph<G>> for u128 {
  fn from(value: UIntGlyph<G>) -> Self {
    value.1
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u64 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u64::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u32 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u32::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u16 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u16::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> TryFrom<UIntGlyph<G>> for u8 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value =
      u8::try_from(value.1).map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Glyph> PartialEq for UIntGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.1 == other.1
  }
}

impl<G: Glyph> Eq for UIntGlyph<G> {}

impl<G: Glyph> PartialOrd for UIntGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for UIntGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.1.cmp(&other.1)
  }
}

impl<G: Glyph> Debug for UIntGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    self.1.fmt(f)
  }
}

impl<G: Glyph> EncodedGlyph<G> for UIntGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
  }
}

/// A glyph containing a floating point number.
///
/// Currently, only `f32` and `f64` are supported, the latter of which is
/// returned by [`Deref`].  However, note that there is also a direct [`From`]
/// implementation from this type into a `f32`.
pub struct FloatGlyph<G: Glyph>(G, f64);

impl<G: Glyph> FloatGlyph<G> {
  /// Returns the value in the glyph.
  pub fn get(&self) -> &f64 {
    &self.1
  }
}

impl<G: Glyph> FromGlyph<G> for FloatGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(Float) {
      return Err(err.into_fge(glyph));
    }
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

impl<G: Glyph> Deref for FloatGlyph<G> {
  type Target = f64;

  fn deref(&self) -> &Self::Target {
    &self.1
  }
}

impl<G: Glyph> From<FloatGlyph<G>> for f32 {
  fn from(value: FloatGlyph<G>) -> Self {
    value.1 as f32
  }
}

impl<G: Glyph> PartialEq for FloatGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for FloatGlyph<G> {}

impl<G: Glyph> PartialOrd for FloatGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for FloatGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    f64::total_cmp(&self.1, &other.1)
  }
}

impl<G: Glyph> Debug for FloatGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    self.1.fmt(f)
  }
}

impl<G: Glyph> EncodedGlyph<G> for FloatGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.0.borrow()
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

gen_prim_from_glyph!(u8, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  ParsedGlyph,
>| { u8::try_from(*gl) });
gen_prim_from_glyph!(u16, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  ParsedGlyph,
>| { u16::try_from(*gl) });
gen_prim_from_glyph!(u32, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  ParsedGlyph,
>| { u32::try_from(*gl) });
gen_prim_from_glyph!(u64, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  ParsedGlyph,
>| { u64::try_from(*gl) });
gen_prim_from_glyph!(u128, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  ParsedGlyph,
>| {
  u128::try_from(*gl)
});
gen_prim_from_glyph!(i8, try_conv_glyph, IntGlyph, |gl: IntGlyph<
  ParsedGlyph,
>| { i8::try_from(*gl) });
gen_prim_from_glyph!(i16, try_conv_glyph, IntGlyph, |gl: IntGlyph<
  ParsedGlyph,
>| { i16::try_from(*gl) });
gen_prim_from_glyph!(i32, try_conv_glyph, IntGlyph, |gl: IntGlyph<
  ParsedGlyph,
>| { i32::try_from(*gl) });
gen_prim_from_glyph!(i64, try_conv_glyph, IntGlyph, |gl: IntGlyph<
  ParsedGlyph,
>| { i64::try_from(*gl) });
gen_prim_from_glyph!(i128, try_conv_glyph, IntGlyph, |gl: IntGlyph<
  ParsedGlyph,
>| {
  i128::try_from(*gl)
});
gen_prim_from_glyph!(f32, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| {
  (*gl) as f32
});
gen_prim_from_glyph!(f64, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| { *gl });
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
