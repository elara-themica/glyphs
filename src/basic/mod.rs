//! Numbers, strings, boolean, nothing, option, etc...
use crate::{
  zerocopy::{
    bounds_check, round_to_word, ZeroCopy, F32, F64, I128, I16, I32, I64, U128,
    U16, U32, U64,
  },
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType,
  GlyphType::{Float, SignedInt, UnsignedInt},
  ParsedGlyph, ToGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  ops::Deref,
  str::from_utf8,
};

mod bitvec;
pub use bitvec::*;

mod zc;
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
  B: Glyph,
  T: FromGlyph<B>,
{
  fn from_glyph(source: B) -> Result<Self, GlyphErr> {
    let type_id = source.header().glyph_type();
    if type_id == GlyphType::Nothing {
      return Ok(None);
    } else {
      let val = T::from_glyph(source)?;
      Ok(Some(val))
    }
  }
}

impl ToGlyph for () {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Nothing, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl<G> FromGlyph<G> for ()
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Nothing)?;
    Ok(())
  }
}

/// A glyph that represents the concept of nothingness--like zero but broader
/// than the concept of numbers.
///
/// Can be created by encoding the rust unit type `()`.
pub struct NothingG<G>(G)
where
  G: Glyph;

impl<G> FromGlyph<G> for NothingG<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Nothing)?;
    Ok(NothingG(source))
  }
}

impl<G> Debug for NothingG<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "NothingGlyph")
  }
}

impl<T: Glyph> PartialEq for NothingG<T> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<T: Glyph> Eq for NothingG<T> {}

impl<T: Glyph> PartialOrd for NothingG<T> {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl<T> Ord for NothingG<T>
where
  T: Glyph,
{
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// Represents the concept that some information exists, but has been removed,
/// e.g., for security or confidentiality.
#[derive(Copy, Clone, Debug)]
pub struct Redacted;

impl<G> FromGlyph<G> for Redacted
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Redacted)?;
    Ok(Redacted)
  }
}

impl ToGlyph for Redacted {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Redacted, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl Eq for Redacted {}

impl PartialEq for Redacted {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl PartialOrd for Redacted {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl Ord for Redacted {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// A glyph representing the concept of some information that exists, but which
/// has been removed, e.g., for security or confidentiality.
///
/// See also [`Redacted`].
pub struct RedactedG<G: Glyph>(G);

impl<G: Glyph> FromGlyph<G> for RedactedG<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Redacted)?;
    Ok(RedactedG(source))
  }
}

impl<G: Glyph> Debug for RedactedG<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "RedactedGlyph")
  }
}

impl<G: Glyph> PartialEq for RedactedG<G> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<G: Glyph> Eq for RedactedG<G> {}

impl<G: Glyph> PartialOrd for RedactedG<G> {
  fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
    Some(Ordering::Equal)
  }
}

impl<G: Glyph> Ord for RedactedG<G> {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// Something that is unknown.
///
/// See also [`UnknownG`].
#[derive(Copy, Clone, Debug)]
pub struct Unknown;

impl<G: Glyph> FromGlyph<G> for Unknown {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Unknown)?;
    Ok(Unknown)
  }
}

impl ToGlyph for Unknown {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new_short(GlyphType::Unknown, [0; 4]).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl Eq for Unknown {}

impl PartialEq for Unknown {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl PartialOrd for Unknown {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(Ord::cmp(self, other))
  }
}

impl Ord for Unknown {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

/// A glyph representing the concept of something that is unknown.
///
/// This is distinct from a [`NothingG`] in that the latter is an assertion
/// that no value is present.
pub struct UnknownG<G: Glyph>(G);

impl<G: Glyph> FromGlyph<G> for UnknownG<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Unknown)?;
    Ok(UnknownG(source))
  }
}

impl<G: Glyph> Debug for UnknownG<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "UnknownGlyph")
  }
}

impl<G: Glyph> PartialEq for UnknownG<G> {
  fn eq(&self, _other: &Self) -> bool {
    true
  }
}

impl<G: Glyph> Eq for UnknownG<G> {}

impl<G: Glyph> PartialOrd for UnknownG<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(Ord::cmp(self, other))
  }
}

impl<G: Glyph> Ord for UnknownG<G> {
  fn cmp(&self, _other: &Self) -> Ordering {
    Ordering::Equal
  }
}

impl ToGlyph for bool {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let bytes = match self {
      true => [1u8, 0, 0, 0],
      false => [0u8; 4],
    };
    GlyphHeader::new_short(GlyphType::Bool, bytes).bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

impl<G> FromGlyph<G> for bool
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::Bool)?;
    let content = source.short_content();
    let value = u32::from_le_bytes(*content);
    Ok(value != 0)
  }
}

/// A glyph containing a boolean value.
///
pub struct BoolG<G: Glyph>(G);

impl<G: Glyph> BoolG<G> {
  /// Fetches the glyph's truth value.
  ///
  /// `BoolGlyph`s are short glyphs, with the content stored in the length
  /// filed of the [`GlyphHeader`].  If all of these bytes are zero, the truth
  /// value will be `false`.  In all other conditions, it will be `true`.
  pub fn get(&self) -> bool {
    self.0.header().short_content() != &[0u8; 4]
  }
}

impl<G: Glyph> FromGlyph<G> for BoolG<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.confirm_type(GlyphType::Bool)?;
    Ok(BoolG(source))
  }
}

impl<G: Glyph> Debug for BoolG<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    if !f.alternate() {
      Debug::fmt(&self.get(), f)
    } else {
      let mut df = f.debug_tuple("BoolGlyph");
      df.field(&self.0);
      df.finish()
    }
  }
}

impl<G: Glyph> PartialEq for BoolG<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for BoolG<G> {}

impl<G: Glyph> PartialOrd for BoolG<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for BoolG<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

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

impl<G: Glyph> FromGlyph<G> for IntGlyph<G> {
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

/// A glyph containing an unsigned integer.
///
/// Currently, values up to a `u128` are supported, which is what will be
/// returned by [`Deref`].  However, note that there are [`TryFrom`]
/// implementations for the smaller unsigned integer types.
pub struct UIntGlyph<G: Glyph>(G, u128);

impl<G: Glyph> FromGlyph<G> for UIntGlyph<G> {
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

/// A glyph containing a floating point number.
///
/// Currently, only `f32` and `f64` are supported, the latter of which is
/// returned by [`Deref`].  However, note that there is also a direct [`From`]
/// implementation from this type into a `f32`.
pub struct FloatGlyph<G: Glyph>(G, f64);

impl<G: Glyph> FromGlyph<G> for FloatGlyph<G> {
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

gen_prim_from_glyph!(u8, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u8::try_from(*gl)
});
gen_prim_from_glyph!(u16, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u16::try_from(*gl)
});
gen_prim_from_glyph!(u32, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u32::try_from(*gl)
});
gen_prim_from_glyph!(u64, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u64::try_from(*gl)
});
gen_prim_from_glyph!(u128, try_conv_glyph, UIntGlyph, |gl: UIntGlyph<G>| {
  u128::try_from(*gl)
});
gen_prim_from_glyph!(i8, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i8::try_from(*gl)
});
gen_prim_from_glyph!(i16, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i16::try_from(*gl)
});
gen_prim_from_glyph!(i32, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i32::try_from(*gl)
});
gen_prim_from_glyph!(i64, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
  i64::try_from(*gl)
});
gen_prim_from_glyph!(i128, try_conv_glyph, IntGlyph, |gl: IntGlyph<G>| {
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

impl<'a> FromGlyph<ParsedGlyph<'a>> for &'a str {
  fn from_glyph(source: ParsedGlyph<'a>) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    let str_bytes = source.content_parsed();
    let valid_str = from_utf8(str_bytes)?;
    Ok(valid_str)
  }
}

impl ToGlyph for str {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // SAFETY: So we can do one bounds check.
    unsafe {
      let str_bytes = self.as_bytes();
      let header = GlyphHeader::new(GlyphType::StringUTF8, str_bytes.len())?;
      let bounds =
        round_to_word(*cursor + size_of::<GlyphHeader>() + str_bytes.len());
      bounds_check(target, bounds)?;
      let mut zero_idx = bounds - 8;
      U64::from(0).bbwr_u(target, &mut zero_idx);
      header.bbwr_u(target, cursor);
      u8::bbwrs_u(str_bytes, target, cursor);
      *cursor = round_to_word(*cursor);
      // pad_to_word_u(target, cursor);
    }
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    round_to_word(size_of::<GlyphHeader>() + self.len())
  }
}

#[cfg(feature = "alloc")]
impl<G> FromGlyph<G> for alloc::string::String
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    let bytes = source.content();
    let bytes_v = u8::bbrds_i(bytes, &mut 0)?;
    let valid_string = alloc::string::String::from_utf8(bytes_v)?;
    Ok(valid_string)
  }
}

#[cfg(feature = "alloc")]
impl ToGlyph for alloc::string::String {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.as_str().glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.as_str().glyph_len()
  }
}

/// A glyph containing a valid UTF-8 string.
pub struct StringGlyph<G>(G)
where
  G: Glyph;

impl<G> StringGlyph<G>
where
  G: Glyph,
{
  /// The string contained in the glyph.
  pub fn get(&self) -> &str {
    let bytes = self.0.content();
    // Validity was already checked during `glyph_decode`.
    unsafe { core::str::from_utf8_unchecked(bytes) }
  }
}

impl<G> Debug for StringGlyph<G>
where
  G: Glyph,
{
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "Utf8Glyph(\"{}\")", self.get())
  }
}

impl<G> FromGlyph<G> for StringGlyph<G>
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::StringUTF8)?;
    // Check for valid UTF-8 string.
    let _ = from_utf8(source.content())?;
    Ok(StringGlyph(source))
  }
}

impl<G: Glyph> PartialEq for StringGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for StringGlyph<G> {}

impl<G: Glyph> PartialOrd for StringGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for StringGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    let a = self.get();
    let b = other.get();
    a.cmp(b)
  }
}

impl<G> FromGlyph<G> for char
where
  G: Glyph,
{
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    let value: u32 =
      U32::bbrd(&source.header().short_content()[..], &mut 0)?.into();
    match char::try_from(value) {
      Ok(c) => Ok(c),
      Err(_err) => Err(GlyphErr::IllegalValue),
    }
  }
}

impl ToGlyph for char {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let value = unsafe { core::mem::transmute::<&char, &[u8; 4]>(&self) };
    GlyphHeader::new_short(GlyphType::UnicodeChar, *value)
      .bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
  }
}

/// A glyph containing a unicode character `char`.
pub struct CharGlyph<G: Glyph>(G);

impl<G: Glyph> CharGlyph<G> {
  /// The `char` contained by this glyph.
  pub fn get(&self) -> char {
    let bytes = self.0.header().short_content();
    // SAFETY: A valid value was confirmed when the CharGlyph was created.
    unsafe { char::from_u32_unchecked(u32::from_le_bytes(*bytes)) }
  }
}

impl<G: Glyph> FromGlyph<G> for CharGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::UnicodeChar)?;
    // Check for valid unicode char.
    let _value = <char>::from_glyph(source.borrow())?;
    Ok(CharGlyph(source))
  }
}

impl<G: Glyph> Debug for CharGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "CharGlyph({:?})", self.get())
  }
}

impl<G: Glyph> PartialEq for CharGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.get() == other.get()
  }
}

impl<G: Glyph> Eq for CharGlyph<G> {}

impl<G: Glyph> PartialOrd for CharGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for CharGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.get().cmp(&other.get())
  }
}

#[cfg(feature = "alloc")]
#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    glyph_new, glyph_read,
    util::{
      debug::HexDump, simple_codec_slice_test, simple_codec_test,
      BENCH_BUF_SIZE,
    },
    FromGlyph, Glyph, GlyphErr,
  };
  use ::test::Bencher;
  use alloc::boxed::Box;
  use std::{dbg, hint::black_box, iter::repeat, string::String};

  #[test]
  fn codec_basic() {
    //== Simple Scalar Values ==/
    simple_codec_test(());
    simple_codec_test(Unknown);
    simple_codec_test(Redacted);
    simple_codec_test(Option::<u32>::None);
    simple_codec_test(Option::<u32>::Some(0xDEAD_BEEF));
    simple_codec_test(42u8);
    simple_codec_test(0xF00Du16);
    simple_codec_test(0xDEADBEEFu32);
    simple_codec_test(0xF00DDEADBEEFF00Du64);
    simple_codec_test(0x0102030405060708090A0B0C0D0E0Fu128);
    simple_codec_test(-8i8);
    simple_codec_test(-16i16);
    simple_codec_test(-32i32);
    simple_codec_test(-64i64);
    simple_codec_test(-128i128);

    //== Simple Slices ==/
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
  }

  macro_rules! gen_bench {
    ($enc_bench_name:ident, $dec_bench_name:ident, $prim:ty) => {
      #[bench]
      fn $enc_bench_name(b: &mut Bencher) -> Result<(), $crate::GlyphErr> {
        let mut buf: Box<[u8]> = repeat(0).take(BENCH_BUF_SIZE).collect();

        // let mut buf =
        //   $crate::buffers::ByteBuffer::new(BENCH_BUF_SIZE, true).unwrap();
        let value: $prim = Default::default();

        // Write the buffer
        b.bytes = BENCH_BUF_SIZE as u64;
        b.iter(|| {
          let cursor = &mut 0;
          loop {
            $crate::ToGlyph::glyph_encode(&value, buf.as_mut(), cursor)?;
          }
          #[allow(unreachable_code)]
          Result::<(), $crate::GlyphErr>::Ok(())
        });
        let _ = black_box(buf);
        Ok(())
      }

      #[bench]
      fn $dec_bench_name(b: &mut Bencher) -> Result<(), $crate::GlyphErr> {
        let mut buf: alloc::boxed::Box<[u8]> =
          core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
        // let mut buf = ByteBuffer::new(BENCH_BUF_SIZE, true).unwrap();
        let value: $prim = Default::default();

        // Write the buffer
        let cursor = &mut 0;
        while *cursor
          <= BENCH_BUF_SIZE
            - size_of::<$prim>()
            - size_of::<$crate::GlyphHeader>()
        {
          $crate::ToGlyph::glyph_encode(&value, buf.as_mut(), cursor)?;
        }

        // Read all the glyphs from the buffer
        b.bytes = BENCH_BUF_SIZE as u64;
        b.iter(|| {
          let cursor = &mut 0;
          loop {
            let glyph = $crate::glyph_read(&buf, cursor)?;
            let _decoded = <$prim>::from_glyph(glyph)?;
          }
          #[allow(unreachable_code)]
          Ok::<(), $crate::GlyphErr>(())
        });
        Ok(())
      }
    };
  }

  gen_bench!(enc_glyph_u8, dec_glyph_u8, u8);
  gen_bench!(enc_glyph_u16, dec_glyph_u16, u16);
  gen_bench!(enc_glyph_u32, dec_glyph_u32, u32);
  gen_bench!(enc_glyph_u64, dec_glyph_u64, u64);

  #[bench]
  fn dec_basic_glyph_i32(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value: i32 = 1;

    // Write the buffer
    let cursor = &mut 0;
    while *cursor <= BENCH_BUF_SIZE - size_of::<i32>() {
      value.glyph_encode(buf.as_mut(), cursor).unwrap();
    }

    dbg!(&HexDump(buf.as_ref()));

    let mut outside = 0i128;

    // Read all the glyphs from the buffer
    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        let glyph = glyph_read(&buf, cursor)?;
        let decoded = IntGlyph::from_glyph(glyph)?;
        outside = *decoded;
      }
      #[allow(unreachable_code)]
      Ok::<(), GlyphErr>(())
    });
    Ok(())
  }

  #[test]
  fn codec_glyph_str() -> Result<(), GlyphErr> {
    // Basic encoding
    let text = "hunter2";
    let glyph = glyph_new(text)?;
    dbg!(&glyph);

    let read_str = <&str>::from_glyph(glyph.borrow())?;
    assert_eq!(read_str, text);

    let read_string = String::from_glyph(glyph.borrow())?;
    assert_eq!(read_string.as_str(), text);

    let str_glyph = StringGlyph::from_glyph(glyph.borrow())?;
    assert_eq!(str_glyph.get(), text);

    Ok(())
  }

  #[bench]
  fn enc_glyph_str(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = "My xenoscience studies range from urban to agrarian, \
                 I am the very model of a scientist Salarian!";

    let target = buf.as_mut();
    let glyph = glyph_new(value)?;
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        value.glyph_encode(target, cursor)?
      }
      #[allow(unreachable_code)]
      Result::<(), GlyphErr>::Ok(())
    });

    let cursor = &mut 0;
    for _ in 0..iterations {
      let glyph = glyph_read(&buf, cursor)?;
      let as_read = <&str>::from_glyph(glyph)?;
      assert_eq!(value, as_read);
    }
    Ok(())
  }

  #[bench]
  fn dec_glyph_str(b: &mut Bencher) -> Result<(), GlyphErr> {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = "My xenoscience studies range from urban to agrarian, \
                 I am the very model of a scientist Salarian!";

    let glyph = glyph_new(value)?;
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    let cursor = &mut 0;
    for _ in 0..iterations {
      value.glyph_encode(buf.as_mut(), cursor)?;
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..iterations {
        let glyph = glyph_read(&buf, cursor)?;
        let _ = <&str>::from_glyph(glyph)?;
      }
      Ok::<(), GlyphErr>(())
    });
    Ok(())
  }

  #[test]
  fn codec_glyph_char() {
    let value = 'K';
    let glyph = glyph_new(&value).unwrap();
    let as_read = char::from_glyph(glyph).unwrap();
    assert_eq!(value, as_read);
  }

  #[bench]
  fn enc_glyph_char(b: &mut Bencher) {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = 'K';

    let glyph = glyph_new(&value).unwrap();
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      loop {
        value.glyph_encode(buf.as_mut(), cursor)?
      }
      #[allow(unreachable_code)]
      Ok::<(), GlyphErr>(())
    });

    let cursor = &mut 0;
    for _ in 0..iterations {
      let glyph = glyph_read(&buf, cursor).unwrap();
      let as_read = char::from_glyph(glyph).unwrap();
      assert_eq!(value, as_read);
    }
  }

  #[bench]
  fn dec_glyph_char(b: &mut Bencher) {
    let mut buf: alloc::boxed::Box<[u8]> =
      core::iter::repeat(0).take(BENCH_BUF_SIZE).collect();
    let value = 'K';

    let glyph = glyph_new(&value).unwrap();
    let iterations = BENCH_BUF_SIZE / glyph.glyph_len();

    let cursor = &mut 0;
    for _ in 0..iterations {
      value.glyph_encode(buf.as_mut(), cursor).unwrap();
    }

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let cursor = &mut 0;
      for _ in 0..iterations {
        let glyph = glyph_read(&buf, cursor)?;
        let _ = char::from_glyph(glyph)?;
      }
      Ok::<(), GlyphErr>(())
    });
  }

  #[bench]
  fn validate_utf8(b: &mut Bencher) {
    let value = b"My xenoscience studies range from urban to agrarian, \
               I am the very model of a scientist Salarian!";

    let iterations = BENCH_BUF_SIZE / value.len();

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let mut sum: u64 = 0;
      for _ in 0..iterations {
        let as_str = from_utf8(&value[..])?;
        sum += as_str.as_bytes()[0] as u64;
      }
      Ok::<u64, core::str::Utf8Error>(sum)
    })
  }
}
