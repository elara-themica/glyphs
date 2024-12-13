//! Serialization with the `serde` library.
//!
//! Mappings:
//!
//! - Individual primitives (e.g., a `u32`) are encoded as a glyph of the
//!   matching primitive type (e.g., [`U32Glyph`]).
//! - Raw tuples (e.g., `(u32, u32, u32)` are encoded as a [`TupleGlyph`].
//! - Vectors are encoded as a [`VecGlyph`], even when serializing vectors of
//!   primitives like `Vec<u32>`.  This is inefficient because the type
//!   information for the `u32` is repeated for each element.  If you are
//!   serializing these types directly (i.e., not deep within some other
//!   data structure) strongly consider using the native [`ToGlyph`] function
//!   instead.
//! - Unit structures (e.g., `struct A`) are encoded as an empty [`ObjGlyph`]
//!   with type `"A"`.  Deserialization requires the type name to
//!   match.
//! - New-type structures (e.g., `struct B(T)`) are encoded as if they were
//!   of type `T`.
//! - Tuple structures (e.g., `struct B(i32, i32)` are encoded as a
//!   [`ObjGlyph`] with type `"B"` and unnamed fields.
//! - Ordinary Structures (e.g., `struct C { b: u32, a: u32 }`) are encoded
//!   as an [`ObjGlyph`] with type `"C"` and named fields.  The fields will
//!   always be encoded in field name order (as a byte string containing UTF-8)
//! - Enum Variants are encoded like their corresponding structures, but
//!   contained within an outer [`ObjGlyph`] with the type of the enum.  
//!
//! For example:
//!
//! ```rust
//! enum E {
//!   UV,
//!   TV(i32),
//!   SV { b: u32, a: u32 }
//! }
//! ```
//!
//! - `E::NTV` would be encoded as an [`ObjGlyph`] with type `"E"`, containing
//!   a single unnamed field.  The value of that inner field would be another
//!   [`ObjGlyph`], this time of type `"UV"` and containing no fields.
//! - `E::TV` would be encoded as an [`ObjGlyph`] with type `"E"`, containing
//!   a single unnamed field.  The value of that inner field would be another
//!   [`ObjGlyph`], this time of type `"TV"` and containing a single unnamed
//!   field.  That field would contain an [`U32Glyph`].  Note that enum tuple
//!   variants with a single field do not follow the same pattern as similar
//!   structures, which would be treated as a "new-type" struct.
//! - `E::SV` would be encoded as an [`ObjGlyph`] with type `"E"`, containing
//!   a single unnamed field.  The value of that inner field would be another
//!   [`ObjGlyph`], this time of type `"SV"` and containing two named fields.
//!   Despite the declared order of those fields being (b, a), the fields
//!   in the inner [`ObjGlyph`] would be re-ordered to (a, b).
#[warn(missing_docs)]
pub(crate) mod de;
#[warn(missing_docs)]
pub(crate) mod ser;

use crate::{GlyphErr, GlyphType};
use alloc::string::{String, ToString};
use core::fmt::{Debug, Display, Formatter};

/// The error type returned when (de-)serializing types through `serde`.
///
/// Unfortunately, we cannot just use [`GlyphErr`] directly, because `serde`
/// requires custom errors and we don't want to put an allocating type
/// in `GlyphErr` for performance reasons.
#[derive(Debug)]
pub enum SerdeGlyphErr {
  /// A custom text error, provided by the `serde` library itself.
  Custom(String),

  GlyphErr(GlyphErr),

  /// A type name was required for deserialization, but none was present.
  TypeNameMissing,

  /// We were attempting to decode a structure, but the source [`ObjGlyph`]'s
  /// type name did not match the target structure's name.
  TypeNameMismatch,

  /// Attempt to decode a sequence (vec or tuple) from something that was
  /// not a vector or tuple glyph.
  SeqInvalidType,

  /// When de-serializing an `enum`, we need to know which variant it is.
  /// This requires that the `ObjGlyph` specify a variant name, which was
  /// missing.
  VariantNameMissing,

  /// Attempt to deserialize a unit struct or unit enum variant (neither have
  /// fields) from an [`ObjGlyph`] with fields.
  UnexpectedFields,

  /// Attempt to deserialize a tuple (or tuple struct or tuple variant) from an
  /// object with named fields.
  TupleNamedFields,

  /// Attempt to deserialize an `enum` variant or `struct` with named fields
  /// from an [`ObjGlyph`] with unnamed fields.
  StructUnnamedFields,

  /// When serializing a sequence, we need to know its length.
  ///
  /// Knowing the length is required to allocate space for offset tables.
  SeqLengthRequired,

  /// When serializing a map, we need to know its length.
  ///
  /// Knowing the length is required to allocate space for offset tables.
  MapLengthRequired,

  /// The Serde deserializer cannot decode this type of glyph.
  InvalidSourceGlyphType(GlyphType),

  /// An attempt to deserialize the value of a structure's field was made before
  /// deserializing the corresponding key.  This is an error caused by the
  /// target type's [`Deserialize`] implementation.
  ///
  /// The API for deserializing field names and values requires that the key
  /// be deserialized first, as only `next_key_seed` allows a [`Deserializer`]
  /// to respond that there are no more key/pairs available.
  ///
  /// It could be caused by attempting to deserialize the field value first, or
  /// by doing it twice before asking for the next key.
  StructFieldValueMissing,

  /// An internal error--some sections of code should never be called.
  Unreachable,
  InvalidSourceGlyphTypeEnum(GlyphType),
}

impl Display for SerdeGlyphErr {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    Debug::fmt(self, f)
  }
}

impl std::error::Error for SerdeGlyphErr {}

impl serde::de::Error for SerdeGlyphErr {
  fn custom<T>(msg: T) -> Self
  where
    T: Display,
  {
    let s = msg.to_string();
    Self::Custom(s)
  }
}

impl serde::ser::Error for SerdeGlyphErr {
  fn custom<T>(msg: T) -> Self
  where
    T: Display,
  {
    let s = msg.to_string();
    Self::Custom(s)
  }
}

impl From<SerdeGlyphErr> for GlyphErr {
  fn from(value: SerdeGlyphErr) -> Self {
    match value {
      SerdeGlyphErr::GlyphErr(ge) => ge,
      _ => GlyphErr::SerdeErr,
    }
  }
}

impl From<GlyphErr> for SerdeGlyphErr {
  fn from(src: GlyphErr) -> Self {
    Self::GlyphErr(src)
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::{
    glyph_new,
    serde::{de::glyph_serde_deserialize, ser::glyph_new_serde},
    structured::ObjGlyph,
    util::init_test_logger,
    FromGlyph, Glyph, ToGlyph,
  };
  use alloc::{collections::BTreeMap, vec::Vec};
  use core::fmt::Debug;
  use serde::{de::DeserializeOwned, Serialize};
  use serde_derive::*;
  use std::{dbg, vec};

  #[test]
  fn serde_primitives() -> Result<(), SerdeGlyphErr> {
    fn compare_primitives<T: ToGlyph + Serialize>(
      val: T,
    ) -> Result<(), SerdeGlyphErr> {
      let native = glyph_new(&val)?;
      let serde = glyph_new_serde(&val)?;
      assert_eq!(&native.as_ref(), &serde.as_ref());
      Ok(())
    }

    compare_primitives(true)?;

    compare_primitives(42i8)?;
    compare_primitives(-1i16)?;
    compare_primitives(1_000_000_000i32)?;
    compare_primitives(12345678i64)?;

    compare_primitives(42u8)?;
    compare_primitives(1u16)?;
    compare_primitives(1_000_000_000u32)?;
    compare_primitives(12345678u64)?;

    compare_primitives(std::f32::consts::E)?;
    compare_primitives(std::f64::consts::PI)?;

    compare_primitives('🦋')?;
    compare_primitives("Glyph")?;
    Ok(())
  }

  /// Confirms round-trip encoding of a raw tuple (`(i32, &str)`, etc...)
  #[test]
  fn serde_basic_tuple() -> Result<(), SerdeGlyphErr> {
    let src = (0xDEAD_BEEFu32, '🦋', "ABC");
    let direct_glyph = glyph_new(&src)?;
    let serde_glyph = glyph_new_serde(&src)?;
    assert_eq!(&direct_glyph.as_ref(), &serde_glyph.as_ref());

    // Test serde decoding
    let (a, b, c) =
      glyph_serde_deserialize::<(u32, char, &str)>(serde_glyph.borrow())?;
    assert_eq!((a, b, c), src);

    Ok(())
  }

  #[test]
  fn serde_sequence() {
    init_test_logger();

    // Test length first
    let s = vec!["itsy", "bitsy", "spider"];

    // Now actually encode something.
    let native_glyph = glyph_new(&s).unwrap();
    let serde_glyph = glyph_new_serde(&s).unwrap();
    dbg!(&native_glyph);
    dbg!(&serde_glyph);
    assert_eq!(native_glyph.as_ref(), serde_glyph.as_ref());

    //== Decoding ==/
    // This section is complex because we should be able to correctly decode
    // both standard VecGlyphs as well as the specialized (e.g. VecU32Glyph)
    // glyphs.
    let decoded =
      glyph_serde_deserialize::<Vec<&str>>(serde_glyph.borrow()).unwrap();
    assert_eq!(&s, &decoded);

    // Decoding specialized vectors of primitives.
    fn decode_specialized<T>(src: Vec<T>) -> Result<(), SerdeGlyphErr>
    where
      T: PartialEq + Debug + ToGlyph + Serialize + DeserializeOwned,
    {
      let native = glyph_new(&src).unwrap();
      let serde = glyph_new_serde(&src).unwrap();
      let decoded = glyph_serde_deserialize::<Vec<T>>(native.borrow()).unwrap();
      assert_eq!(&decoded, &src);
      let decoded = glyph_serde_deserialize::<Vec<T>>(serde.borrow()).unwrap();
      assert_eq!(&decoded, &src);
      Ok(())
    }

    decode_specialized(vec![true, false, true, false]).unwrap();
    decode_specialized(vec![-1i8, 2, -3]).unwrap();
    decode_specialized(vec![-1i16, 2, -3]).unwrap();
    decode_specialized(vec![-1i32, 2, -3]).unwrap();
    decode_specialized(vec![-1i64, 2, -3]).unwrap();
    decode_specialized(vec![1u8, 2, 3]).unwrap();
    decode_specialized(vec![1u16, 2, 3]).unwrap();
    decode_specialized(vec![1u32, 2, 3]).unwrap();
    decode_specialized(vec![1u64, 2, 3]).unwrap();

    decode_specialized(vec![1.0f32, -2.0, 3.0]).unwrap();
    decode_specialized(vec![1.0f64, -2.0, 3.0]).unwrap();
  }

  #[test]
  fn serde_map() -> Result<(), SerdeGlyphErr> {
    let mut map = BTreeMap::new();
    map.insert(1, 2);
    map.insert(2, 4);
    map.insert(3, 8);

    let native = glyph_new(&map)?;
    let serde = glyph_new_serde(&map)?;

    dbg!(&native, &serde);
    assert_eq!(native.content(), serde.content());

    let decoded: BTreeMap<i32, i32> = glyph_serde_deserialize(native.borrow())?;
    assert_eq!(&map, &decoded);

    Ok(())
  }

  #[test]
  fn serde_unit_struct() -> Result<(), SerdeGlyphErr> {
    #[derive(Serialize, Deserialize)]
    struct Empty;

    #[derive(Serialize, Deserialize)]
    struct AlsoEmpty;

    // Can't compare, because there's currently no native method to
    // serialize an arbitrary test structure.  So we'll just look at the
    // binary format for now.
    let unit_struct = glyph_new_serde(&Empty)?;
    dbg!(unit_struct.borrow());
    let obj_glyph = ObjGlyph::from_glyph(unit_struct.borrow())?;
    dbg!(&obj_glyph);

    // Nothing to compare, but check that deserialization passes type checks.
    let _decoded: Empty = glyph_serde_deserialize(unit_struct.borrow())?;

    // When deserializing an object with a different name, we should get
    // an error.
    assert!(glyph_serde_deserialize::<AlsoEmpty>(unit_struct.borrow()).is_err());
    Ok(())
  }

  #[test]
  fn serde_newtype_struct() -> Result<(), SerdeGlyphErr> {
    #[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
    struct NewTypeStruct(u32);

    let nts = NewTypeStruct(42u32);
    let ntsg = glyph_new_serde(&nts)?;
    dbg!(&ntsg);

    let native_decode = u32::from_glyph(ntsg.borrow())?;
    assert_eq!(native_decode, 42);

    let serde_decode = glyph_serde_deserialize::<NewTypeStruct>(ntsg.borrow())?;
    assert_eq!(nts, serde_decode);

    Ok(())
  }

  #[test]
  fn serde_tuple_struct() {
    init_test_logger();
    log::trace!("foo");

    #[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
    struct TupleStruct<'a>(u32, (), &'a str);

    let a = TupleStruct(5, (), "foo");
    let encoded = glyph_new_serde(&a).unwrap();
    // std::println!("{encoded:#?}");
    let b: TupleStruct = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);
    let decoded = ObjGlyph::from_glyph(encoded).unwrap();
    // std::println!("{decoded:#?}");
    assert_eq!(decoded.len(), 3);
    assert!(!decoded.has_field_names());
    assert_eq!(decoded.type_name(), Some("TupleStruct"))
  }

  #[test]
  fn serde_struct() {
    #[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
    struct Struct<'a> {
      first:  u32,
      second: &'a str,
    }

    let a = Struct {
      first:  9,
      second: "foo",
    };
    let encoded = glyph_new_serde(&a).unwrap();
    std::println!("{encoded:#?}");
    let b: Struct = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);
    let decoded = ObjGlyph::from_glyph(encoded).unwrap();
    std::println!("{decoded:#?}");
  }

  #[test]
  fn serde_enums() {
    #[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
    enum Enum {
      Unit,
      NewType(u32),
      Tuple(u8, u8, u8),
      Struct { first: u32, second: String },
    }

    let a = Enum::Unit;
    let encoded = glyph_new_serde(&a).unwrap();
    // std::println!("{encoded:#?}");
    let b: Enum = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);

    let a = Enum::NewType(42);
    let encoded = glyph_new_serde(&a).unwrap();
    // std::println!("{encoded:#?}");
    let b: Enum = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);

    let a = Enum::Tuple(1, 2, 3);
    let encoded = glyph_new_serde(&a).unwrap();
    // std::println!("{encoded:#?}");
    let b: Enum = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);

    let a = Enum::Struct {
      first:  5,
      second: "ANXIETY".to_string(),
    };
    let encoded = glyph_new_serde(&a).unwrap();
    // std::println!("{encoded:#?}");
    let b: Enum = glyph_serde_deserialize(encoded.borrow()).unwrap();
    assert_eq!(a, b);
  }
}
