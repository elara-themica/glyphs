use crate::{
  zerocopy::{ZeroCopy, F32, F64, I128, I16, I32, I64, U128, U16, U32, U64},
  EncodedGlyph, FromGlyph, Glyph, GlyphDecodeErr, GlyphErr, GlyphType,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};
use num_bigint::{BigInt, BigUint, Sign};
use std::ops::Deref;

/// Signed integers
///
/// 32-, 64-, and 128-bit versions are supported.
///
///
///
/// ```
/// use glyphs::{Glyph, FromGlyph};
///
/// // 32-bit encoding and decoding
/// let g = Glyph::new(42i32).unwrap();
/// assert_eq!(g.glyph_len(), 8);
/// let decoded = i32::from_glyph(g).unwrap();
/// assert_eq!(decoded, 42i32);
///
///
///
/// ```
#[derive(Copy, Clone)]
pub struct IntGlyph<G: Deref<Target = Glyph>>(G);

impl<G: Deref<Target = Glyph>> IntGlyph<G> {
  /// Returns the value as an i32 or an overflow error.
  pub fn get_i32(&self) -> Result<i32, GlyphErr> {
    if self.0.header().is_short() {
      Ok(i32::from_le_bytes(*self.0.header().short_content()))
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => i32::try_from(I64::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        16 => i32::try_from(I128::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        _ => {
          let bi = BigInt::from_signed_bytes_le(buf);
          i32::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an i64 or an overflow error.
  pub fn get_i64(&self) -> Result<i64, GlyphErr> {
    if self.0.header().is_short() {
      Ok(i32::from_le_bytes(*self.0.header().short_content()) as i64)
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => Ok(I64::bbrf(buf, &mut 0)?.get()),
        16 => i64::try_from(I128::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        _ => {
          let bi = BigInt::from_signed_bytes_le(buf);
          i64::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an i128 or an overflow error.
  pub fn get_i128(&self) -> Result<i128, GlyphErr> {
    if self.0.header().is_short() {
      Ok(i32::from_le_bytes(*self.0.header().short_content()) as i128)
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => Ok(I64::bbrf(buf, &mut 0)?.get() as i128),
        16 => Ok(I128::bbrf(buf, &mut 0)?.get()),
        _ => {
          let bi = BigInt::from_signed_bytes_le(buf);
          i128::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an arbitrarily large integer
  pub fn get_big_int(&self) -> BigInt {
    if self.0.header().is_short() {
      BigInt::from_signed_bytes_le(self.0.header().short_content())
    } else {
      let buf = self.0.content_padded();
      BigInt::from_signed_bytes_le(buf)
    }
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for IntGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

impl<G: Deref<Target = Glyph>> Eq for IntGlyph<G> {}

impl<G: Deref<Target = Glyph>> Debug for IntGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "IntGlyph({:?})", self.get_big_int())
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for IntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    match glyph.header().confirm_type(GlyphType::SignedInt) {
      Ok(()) => Ok(IntGlyph(glyph)),
      Err(err) => Err(GlyphDecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Ord for IntGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    // TODO-OPT: Decoding arbitrarily sized `BigInt`s for ordering requires allocation.
    self.get_big_int().cmp(&other.get_big_int())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for IntGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.0.content_padded().eq(other.0.content_padded())
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for IntGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// A glyph containing an unsigned integer.
///
/// Currently, values up to a `u128` are supported, which is what will be
/// returned by [`Deref`].  However, note that there are [`TryFrom`]
/// implementations for the smaller unsigned integer types.
pub struct UIntGlyph<G: Deref<Target = Glyph>>(G);

impl<G: Deref<Target = Glyph>> UIntGlyph<G> {
  /// Returns the value as an i32 or an overflow error.
  pub fn get_u32(&self) -> Result<u32, GlyphErr> {
    if self.0.header().is_short() {
      Ok(u32::from_le_bytes(*self.0.header().short_content()))
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => u32::try_from(U64::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        16 => u32::try_from(U128::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        _ => {
          let bi = BigUint::from_bytes_le(buf);
          u32::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an i64 or an overflow error.
  pub fn get_u64(&self) -> Result<u64, GlyphErr> {
    if self.0.header().is_short() {
      Ok(u32::from_le_bytes(*self.0.header().short_content()) as u64)
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => Ok(U64::bbrf(buf, &mut 0)?.get()),
        16 => u64::try_from(U128::bbrf(buf, &mut 0)?.get())
          .map_err(|_err| GlyphErr::IntConversionOverflow),
        _ => {
          let bi = BigUint::from_bytes_le(buf);
          u64::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an i128 or an overflow error.
  pub fn get_u128(&self) -> Result<u128, GlyphErr> {
    if self.0.header().is_short() {
      Ok(u32::from_le_bytes(*self.0.header().short_content()) as u128)
    } else {
      let buf = self.0.content_padded();
      match buf.len() {
        8 => Ok(U64::bbrf(buf, &mut 0)?.get() as u128),
        16 => Ok(U128::bbrf(buf, &mut 0)?.get()),
        _ => {
          let bi = BigUint::from_bytes_le(buf);
          u128::try_from(bi).map_err(|_err| GlyphErr::IntConversionOverflow)
        },
      }
    }
  }

  /// Returns the value as an arbitrarily large integer
  pub fn get_big_uint(&self) -> BigUint {
    if self.0.header().is_short() {
      BigUint::from_bytes_le(self.0.header().short_content())
    } else {
      let buf = self.0.content_padded();
      BigUint::from_bytes_le(buf)
    }
  }

  /// Returns the value as an arbitrarily large integer
  pub fn get_big_int(&self) -> BigInt {
    if self.0.header().is_short() {
      BigInt::from_bytes_le(Sign::Plus, self.0.header().short_content())
    } else {
      let buf = self.0.content_padded();
      BigInt::from_bytes_le(Sign::Plus, buf)
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for UIntGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "UIntGlyph({})", self.get_big_uint())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for UIntGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

impl<G: Deref<Target = Glyph>> Eq for UIntGlyph<G> {}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for UIntGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    match glyph.header().confirm_type(GlyphType::UnsignedInt) {
      Ok(()) => Ok(UIntGlyph(glyph)),
      Err(err) => Err(GlyphDecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for UIntGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.0.content_padded().eq(other.0.content_padded())
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for UIntGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for UIntGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    // TODO-OPT: Decoding `BitUint` for comparison requires allocation
    self.get_big_uint().cmp(&other.get_big_uint())
  }
}

/// A glyph containing a floating point number.
///
/// Currently, only `f32` and `f64` are supported, the latter of which is
/// returned by [`Deref`].  However, note that there is also a direct [`From`]
/// implementation from this type into a `f32`.
pub struct FloatGlyph<G: Deref<Target = Glyph>>(G);

impl<G: Deref<Target = Glyph>> FloatGlyph<G> {
  /// Returns the value in the glyph as a `f32`
  pub fn get_f32(&self) -> f32 {
    if self.0.header().is_short() {
      f32::from_le_bytes(*self.0.header().short_content())
    } else {
      let buf = self.0.content_padded();
      unsafe {
        match buf.len() {
          8 => F64::bbrf_u(buf, &mut 0).get() as f32,
          _ => todo!("Handle arbitrary precision floats"),
        }
      }
    }
  }

  /// Returns the value in the glyph as a `f32`
  pub fn get_f64(&self) -> f64 {
    if self.0.header().is_short() {
      f32::from_le_bytes(*self.0.header().short_content()) as f64
    } else {
      let buf = self.0.content_padded();
      unsafe {
        match buf.len() {
          8 => F64::bbrf_u(buf, &mut 0).get(),
          _ => todo!("Handle arbitrary precision floats"),
        }
      }
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for FloatGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "FloatGlyph({})", self.get_f64())
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for FloatGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    match glyph.header().confirm_type(GlyphType::Float) {
      Ok(()) => Ok(FloatGlyph(glyph)),
      Err(err) => Err(GlyphDecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for FloatGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0.deref()
  }
}

impl<G: Deref<Target = Glyph>> Eq for FloatGlyph<G> {}

impl<G: Deref<Target = Glyph>> From<FloatGlyph<G>> for f32 {
  fn from(value: FloatGlyph<G>) -> Self {
    value.get_f32()
  }
}

impl<G: Deref<Target = Glyph>> Ord for FloatGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    f64::total_cmp(&self.get_f64(), &other.get_f64())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for FloatGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for FloatGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<IntGlyph<G>> for i8 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value = i8::try_from(value.get_i32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<IntGlyph<G>> for i16 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value = i16::try_from(value.get_i32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<IntGlyph<G>> for i32 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value = i32::try_from(value.get_i32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<IntGlyph<G>> for i64 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    let value = i64::try_from(value.get_i64()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<IntGlyph<G>> for i128 {
  type Error = GlyphErr;

  fn try_from(value: IntGlyph<G>) -> Result<Self, Self::Error> {
    value.get_i128()
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<UIntGlyph<G>> for u8 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value = u8::try_from(value.get_u32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<UIntGlyph<G>> for u16 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value = u16::try_from(value.get_u32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<UIntGlyph<G>> for u32 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value = u32::try_from(value.get_u32()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<UIntGlyph<G>> for u64 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    let value = u64::try_from(value.get_u64()?)
      .map_err(|_err| GlyphErr::IntConversionOverflow)?;
    Ok(value)
  }
}

impl<G: Deref<Target = Glyph>> TryFrom<UIntGlyph<G>> for u128 {
  type Error = GlyphErr;

  fn try_from(value: UIntGlyph<G>) -> Result<Self, Self::Error> {
    Ok(value.get_u128()?)
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

gen_prim_from_glyph!(u32, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  &Glyph,
>| { gl.get_u32() });
gen_prim_from_glyph!(u64, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  &Glyph,
>| { gl.get_u64() });
gen_prim_from_glyph!(u128, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<
  &Glyph,
>| { gl.get_u128() });
gen_prim_from_glyph!(i32, try_conv_glyph, IntGlyph, |gl: IntGlyph<&Glyph>| {
  gl.get_i32()
});
gen_prim_from_glyph!(i64, try_conv_glyph, IntGlyph, |gl: IntGlyph<&Glyph>| {
  gl.get_i64()
});
gen_prim_from_glyph!(i128, try_conv_glyph, IntGlyph, |gl: IntGlyph<&Glyph>| {
  gl.get_i128()
});
gen_prim_from_glyph!(f32, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| {
  gl.get_f32()
});
gen_prim_from_glyph!(f64, conv_glyph, FloatGlyph, |gl: FloatGlyph<G>| {
  gl.get_f64()
});
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
