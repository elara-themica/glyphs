use crate::{
  basic::{
    BasicVecGlyph, BasicVecGlyphHeader, BitVecGlyph, FloatGlyph, IntGlyph,
    UIntGlyph, UnitGlyph, UnitTypes,
  },
  collections::{MapGlyph, TupleGlyph, VecGlyph},
  serde::SerdeGlyphErr,
  structured::ObjGlyph,
  zerocopy::{
    ZeroCopy, ZeroCopyTypeID, F32, F64, I128, I16, I32, I64, U128, U16, U32,
    U64,
  },
  FromGlyph, Glyph, GlyphType, ParsedGlyph,
};
use serde::{
  de::{
    DeserializeSeed, EnumAccess, MapAccess, SeqAccess, VariantAccess, Visitor,
  },
  Deserialize, Deserializer,
};

/// Deserialize a type that implements `serde`'s [`Deserialize`] trait.
///
/// Glyphs are deserialized as follows (which also corresponds to how these
/// types are serialized):
///
/// - _Numeric Primitives_.  Numeric primitives can be deserialized from any
///   valid numeric glyph type, provided there is no overflow.
/// - _Strings_.  [`String`]s and [`str`]s are deserialized from
///  [`StringGlyph`]s, which currently only support the UTF-8 type.
/// - _Options_.  When deserializing an option, a [`NothingGlyph`] will be
///   deserialized as `None`, otherwise it will be a `Some` of the type present.
/// - _Sequences_.  Sequence types can be deserialized from either a
///   [`VecGlyph`] or the various specialized vector glyph types containing
///   primitives, such as [`VecU32Glyph`].
/// - _Tuples_.  Deserialized from [`TupleGlyph`]s.
/// - _Maps_.  Deserialized from [`MapGlyph`]s.
/// - _Structs_.  Deserialized from [`ObjGlyph`]s with matching type names.
///   Unit structs must have no fields, tuple structs must have unnamed fields,
///   and regular structs must have named fields.  Newtype structs are
///   deserialized transparently, e.g., `struct T(U)` can be deserialized from
///   just a `U`.
/// - _Enums_.  Like structs, except (1) the source `ObjGlyph` must contain a
///   variant name, and (2) newtype variants are deserialized from tuple
///   variants with a single field.
pub fn glyph_serde_deserialize<'a, T>(
  glyph: ParsedGlyph<'a>,
) -> Result<T, SerdeGlyphErr>
where
  T: Deserialize<'a>,
{
  let gd = GlyphDeserializer(glyph);
  let t = T::deserialize(gd)?;
  Ok(t)
}

struct GlyphDeserializer<'de>(ParsedGlyph<'de>);

impl<'de> GlyphDeserializer<'de> {
  // fn numbers<V>(&self, visitor: V) -> Result<V::Value, SerdeGlyphErr>
  // where
  //   V: Visitor<'de>,
  // {
  //   let type_id = self.0.type_id_enum();
  //   match type_id {
  //     GlyphType::UnsignedInt => {
  //       let value = u128::from_glyph(self.0)?;
  //       visitor.visit_u128(value)
  //     },
  //     GlyphType::SignedInt => {
  //       let value = i128::from_glyph(self.0)?;
  //       visitor.visit_i128(value)
  //     },
  //     GlyphType::Float => {
  //       let value = f64::from_glyph(self.0)?;
  //       visitor.visit_f64(value)
  //     },
  //     //
  //     //
  //     // GlyphType::U32 => {
  //     //   let value = u32::from_glyph(self.0)?;
  //     //   visitor.visit_u32(value)
  //     // },
  //     // GlyphType::U64 => {
  //     //   let value = u64::from_glyph(self.0)?;
  //     //   visitor.visit_u64(value)
  //     // },
  //     // GlyphType::U128 => {
  //     //   let value = u128::from_glyph(self.0)?;
  //     //   visitor.visit_u128(value)
  //     // },
  //     // GlyphType::I32 => {
  //     //   let value = i32::from_glyph(self.0)?;
  //     //   visitor.visit_i32(value)
  //     // },
  //     // GlyphType::I64 => {
  //     //   let value = i64::from_glyph(self.0)?;
  //     //   visitor.visit_i64(value)
  //     // },
  //     // GlyphType::I128 => {
  //     //   let value = i128::from_glyph(self.0)?;
  //     //   visitor.visit_i128(value)
  //     // },
  //     // GlyphType::F32 => {
  //     //   let value = f32::from_glyph(self.0)?;
  //     //   visitor.visit_f32(value)
  //     // },
  //     // GlyphType::F64 => {
  //     //   let value = f64::from_glyph(self.0)?;
  //     //   visitor.visit_f64(value)
  //     // },
  //     _ => Err(SerdeGlyphErr::InvalidSourceGlyphTypeEnum(type_id)),
  //   }
  // }
}

impl<'de> Deserializer<'de> for GlyphDeserializer<'de> {
  type Error = SerdeGlyphErr;

  fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let type_id = self.0.glyph_type();
    match type_id {
      GlyphType::Object => {
        // Both various enums and structs
        let og = ObjGlyph::from_glyph(self.0)?;
        if og.variant_name().is_some() {
          // Enum
          visitor.visit_enum(ObjEnumAccess(og))
        } else {
          // Struct
          if og.has_field_names() {
            // Regular struct
            let mut it = og.fields_iter_parse();
            let ds = StructAccess {
              it:    &mut it,
              value: None,
            };
            visitor.visit_map(ds)
          } else {
            if og.len() == 0 {
              // Unit struct
              visitor.visit_unit()
            } else {
              // Tuple Struct
              let mut it =
                og.fields_iter_parse().map(|(_field_name, field)| field);
              let ds = IterSeqDeserializer(&mut it);
              visitor.visit_seq(ds)
            }
          }
        }
      },
      GlyphType::Unit => {
        let ug = UnitGlyph::from_glyph(self.0)?;
        if ug.type_id().eq(&UnitTypes::Nothing) {
          visitor.visit_none()
        } else {
          visitor.visit_unit()
        }
      },
      GlyphType::Bool => {
        let value = bool::from_glyph(self.0)?;
        visitor.visit_bool(value)
      },
      GlyphType::UnicodeChar => self.deserialize_char(visitor),
      GlyphType::UnsignedInt => {
        let int = UIntGlyph::from_glyph(self.0)?;
        visitor.visit_u128(*int)
      },
      GlyphType::SignedInt => {
        let int = IntGlyph::from_glyph(self.0)?;
        visitor.visit_i128(*int)
      },
      GlyphType::Float => {
        let float = FloatGlyph::from_glyph(self.0)?;
        visitor.visit_f64(*float)
      },
      GlyphType::Vec => self.deserialize_seq(visitor),
      GlyphType::VecBasic => self.deserialize_seq(visitor),
      GlyphType::VecBool => self.deserialize_seq(visitor),
      GlyphType::String => self.deserialize_str(visitor),
      GlyphType::Map => self.deserialize_map(visitor),
      _ => Err(SerdeGlyphErr::InvalidSourceGlyphType(type_id)),
    }
  }

  fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let value = bool::from_glyph(self.0)?;
    visitor.visit_bool(value)
  }

  fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = i8::from_glyph(self.0)?;
    visitor.visit_i8(val)
  }

  fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = i16::from_glyph(self.0)?;
    visitor.visit_i16(val)
  }

  fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = i32::from_glyph(self.0)?;
    visitor.visit_i32(val)
  }

  fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = i64::from_glyph(self.0)?;
    visitor.visit_i64(val)
  }

  fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = i128::from_glyph(self.0)?;
    visitor.visit_i128(val)
  }

  fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = u8::from_glyph(self.0)?;
    visitor.visit_u8(val)
  }

  fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = u16::from_glyph(self.0)?;
    visitor.visit_u16(val)
  }

  fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = u32::from_glyph(self.0)?;
    visitor.visit_u32(val)
  }

  fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = u64::from_glyph(self.0)?;
    visitor.visit_u64(val)
  }

  fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = u128::from_glyph(self.0)?;
    visitor.visit_u128(val)
  }

  fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = f32::from_glyph(self.0)?;
    visitor.visit_f32(val)
  }

  fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let val = f64::from_glyph(self.0)?;
    visitor.visit_f64(val)
  }

  fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let value = char::from_glyph(self.0)?;
    visitor.visit_char(value)
  }

  fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let value = <&'de str>::from_glyph(self.0)?;
    visitor.visit_borrowed_str(value)
  }

  fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let value = <&'de str>::from_glyph(self.0)?;
    visitor.visit_str(value)
  }

  fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let bytes = <&[u8]>::from_glyph(self.0)?;
    visitor.visit_borrowed_bytes(bytes)
  }

  fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let bytes = <&[u8]>::from_glyph(self.0)?;
    let bytes = alloc::vec::Vec::<u8>::from(bytes);
    visitor.visit_byte_buf(bytes)
  }

  fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    if self.0.glyph_type() == GlyphType::Unit {
      let unit = UnitGlyph::from_glyph(self.0)?;
      if unit.type_id().eq(&UnitTypes::Nothing) {
        visitor.visit_none()
      } else {
        visitor.visit_some(self)
      }
    } else {
      visitor.visit_some(self)
    }
  }

  fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let _ = <()>::from_glyph(self.0)?;
    visitor.visit_unit()
  }

  fn deserialize_unit_struct<V>(
    self,
    name: &'static str,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let og = ObjGlyph::from_glyph(self.0)?;
    let decoded_name = og.type_name().ok_or(SerdeGlyphErr::TypeNameMissing)?;
    if name != decoded_name {
      Err(SerdeGlyphErr::TypeNameMismatch)
    } else if og.len() > 0 {
      Err(SerdeGlyphErr::UnexpectedFields)
    } else {
      let value = visitor.visit_unit::<SerdeGlyphErr>()?;
      Ok(value)
    }
  }

  fn deserialize_newtype_struct<V>(
    self,
    _name: &'static str,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    visitor.visit_newtype_struct(self)
  }

  fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let type_id = self.0.glyph_type();
    match type_id {
      GlyphType::Vec => {
        let vg = VecGlyph::from_glyph(self.0)?;
        let mut iter = vg.iter_parsed();
        let ds = VecDeserializer::VecGlyph(&mut iter);
        visitor.visit_seq(ds)
      },
      GlyphType::Tuple => {
        let vg = TupleGlyph::from_glyph(self.0)?;
        let mut iter = vg.iter_parsed();
        let ds = VecDeserializer::VecGlyph(&mut iter);
        visitor.visit_seq(ds)
      },
      GlyphType::VecBool => {
        let vg = BitVecGlyph::from_glyph(self.0)?;
        let mut it = vg.bit_vector_parsed().iter_parsed();
        let ds = VecDeserializer::BoolIt(&mut it);
        visitor.visit_seq(ds)
      },
      GlyphType::VecBasic => {
        let content = self.0.content_padded();
        let vgh = BasicVecGlyphHeader::bbrf(content, &mut 0)?;
        let zct = vgh.get_zero_copy_type_id();
        match zct {
          ZeroCopyTypeID::U8 => {
            let vg = BasicVecGlyph::<_, u8>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecU8(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::U16 => {
            let vg = BasicVecGlyph::<_, U16>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecU16(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::U32 => {
            let vg = BasicVecGlyph::<_, U32>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecU32(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::U64 => {
            let vg = BasicVecGlyph::<_, U64>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecU64(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::U128 => {
            let vg = BasicVecGlyph::<_, U128>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecU128(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::I8 => {
            let vg = BasicVecGlyph::<_, i8>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecI8(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::I16 => {
            let vg = BasicVecGlyph::<_, I16>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecI16(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::I32 => {
            let vg = BasicVecGlyph::<_, I32>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecI32(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::I64 => {
            let vg = BasicVecGlyph::<_, I64>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecI64(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::I128 => {
            let vg = BasicVecGlyph::<_, I128>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecI128(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::F32 => {
            let vg = BasicVecGlyph::<_, F32>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecF32(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          ZeroCopyTypeID::F64 => {
            let vg = BasicVecGlyph::<_, F64>::from_glyph(self.0)?;
            let ds = VecDeserializer::VecF64(vg.get_parsed());
            visitor.visit_seq(ds)
          },
          _ => Err(SerdeGlyphErr::SeqInvalidType),
        }
      },
      _ => Err(SerdeGlyphErr::SeqInvalidType),
    }
  }

  fn deserialize_tuple<V>(
    self,
    _len: usize,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let tg = TupleGlyph::from_glyph(self.0)?;
    let mut iter = tg.iter_parsed();
    let gd = IterSeqDeserializer(&mut iter);
    let value = visitor.visit_seq(gd)?;
    Ok(value)
  }

  fn deserialize_tuple_struct<V>(
    self,
    name: &'static str,
    _len: usize,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let og = ObjGlyph::from_glyph(self.0)?;
    let type_name = og.type_name().ok_or(SerdeGlyphErr::TypeNameMissing)?;
    if type_name != name {
      Err(SerdeGlyphErr::TypeNameMismatch)
    } else if og.has_field_names() {
      Err(SerdeGlyphErr::TupleNamedFields)
    } else {
      let mut it = og.fields_iter_parse().map(|(_field_name, field)| field);
      let ds = IterSeqDeserializer(&mut it);
      visitor.visit_seq(ds)
    }
  }

  fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let map = MapGlyph::from_glyph(self.0)?;
    visitor.visit_map(MapGlyphAccess {
      iter:       &mut map.iter_parsed(),
      next_value: None,
    })
  }

  fn deserialize_struct<V>(
    self,
    name: &'static str,
    _fields: &'static [&'static str],
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let obj = ObjGlyph::from_glyph(self.0)?;
    let type_name = obj.type_name().ok_or(SerdeGlyphErr::TypeNameMissing)?;
    if type_name != name {
      Err(SerdeGlyphErr::TypeNameMismatch)
    } else if !obj.has_field_names() {
      Err(SerdeGlyphErr::StructUnnamedFields)
    } else {
      let mut it = obj.fields_iter_parse();
      let ds = StructAccess {
        it:    &mut it,
        value: None,
      };
      visitor.visit_map(ds)
    }
  }

  fn deserialize_enum<V>(
    self,
    name: &'static str,
    _variants: &'static [&'static str],
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    let obj = ObjGlyph::from_glyph(self.0)?;
    let type_name = obj.type_name().ok_or(SerdeGlyphErr::TypeNameMissing)?;
    if type_name != name {
      Err(SerdeGlyphErr::TypeNameMismatch)
    } else {
      visitor.visit_enum(ObjEnumAccess(obj))
    }
  }

  fn deserialize_identifier<V>(
    self,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_ignored_any<V>(
    self,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }
}

struct IterSeqDeserializer<'a, 'de>(
  &'a mut dyn Iterator<Item = ParsedGlyph<'de>>,
);

impl<'a, 'de> SeqAccess<'de> for IterSeqDeserializer<'a, 'de> {
  type Error = SerdeGlyphErr;

  fn next_element_seed<T>(
    &mut self,
    seed: T,
  ) -> Result<Option<T::Value>, Self::Error>
  where
    T: DeserializeSeed<'de>,
  {
    match self.0.next() {
      None => Ok(None),
      Some(glyph) => {
        let ds = GlyphDeserializer(glyph);
        let value = seed.deserialize(ds)?;
        Ok(Some(value))
      },
    }
  }
}

enum VecDeserializer<'a, 'de> {
  VecGlyph(&'a mut dyn Iterator<Item = ParsedGlyph<'de>>),
  BoolIt(&'a mut dyn Iterator<Item = bool>),
  VecU8(&'de [u8]),
  VecU16(&'de [U16]),
  VecU32(&'de [U32]),
  VecU64(&'de [U64]),
  VecU128(&'de [U128]),
  VecI8(&'de [i8]),
  VecI16(&'de [I16]),
  VecI32(&'de [I32]),
  VecI64(&'de [I64]),
  VecI128(&'de [I128]),
  VecF32(&'de [F32]),
  VecF64(&'de [F64]),
}

impl<'a, 'de> SeqAccess<'de> for VecDeserializer<'a, 'de> {
  type Error = SerdeGlyphErr;

  fn next_element_seed<T>(
    &mut self,
    seed: T,
  ) -> Result<Option<T::Value>, Self::Error>
  where
    T: DeserializeSeed<'de>,
  {
    match self {
      VecDeserializer::VecGlyph(it) => match it.next() {
        None => Ok(None),
        Some(glyph) => {
          let gs = GlyphDeserializer(glyph);
          let value = seed.deserialize(gs)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::BoolIt(it) => match it.next() {
        None => Ok(None),
        Some(value) => {
          let ds = PassthroughDeserializer::Bool(value);
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecU8(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::U8(*value);
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecU16(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::U16(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecU32(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::U32(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecU64(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::U64(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecU128(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::U128(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecI8(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::I8(*value);
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecI16(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::I16(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecI32(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::I32(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecI64(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::I64(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecI128(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::I128(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecF32(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::F32(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
      VecDeserializer::VecF64(sl) => match sl.split_first() {
        None => Ok(None),
        Some((value, remainder)) => {
          let ds = PassthroughDeserializer::F64(value.get());
          *sl = remainder;
          let value = seed.deserialize(ds)?;
          Ok(Some(value))
        },
      },
    }
  }
}

struct MapGlyphAccess<'a, 'de> {
  iter:       &'a mut dyn Iterator<Item = (ParsedGlyph<'de>, ParsedGlyph<'de>)>,
  next_value: Option<ParsedGlyph<'de>>,
}

impl<'a, 'de> MapAccess<'de> for MapGlyphAccess<'a, 'de> {
  type Error = SerdeGlyphErr;

  fn next_key_seed<K>(
    &mut self,
    seed: K,
  ) -> Result<Option<K::Value>, Self::Error>
  where
    K: DeserializeSeed<'de>,
  {
    if let Some((key, value)) = self.iter.next() {
      self.next_value = Some(value);
      let key = seed.deserialize(GlyphDeserializer(key))?;
      Ok(Some(key))
    } else {
      Ok(None)
    }
  }

  fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
  where
    V: DeserializeSeed<'de>,
  {
    if let Some(value) = self.next_value.take() {
      let value = seed.deserialize(GlyphDeserializer(value))?;
      Ok(value)
    } else {
      Err(SerdeGlyphErr::Unreachable)
    }
  }
}

struct StructAccess<'a, 'de> {
  it:    &'a mut dyn Iterator<Item = (Option<&'de str>, ParsedGlyph<'de>)>,
  value: Option<ParsedGlyph<'de>>,
}

impl<'a, 'de> MapAccess<'de> for StructAccess<'a, 'de> {
  type Error = SerdeGlyphErr;

  fn next_key_seed<K>(
    &mut self,
    seed: K,
  ) -> Result<Option<K::Value>, Self::Error>
  where
    K: DeserializeSeed<'de>,
  {
    match self.it.next() {
      None => Ok(None),
      Some((field_name, field_value)) => {
        // return field name, save field value
        self.value = Some(field_value);
        match field_name {
          None => Err(SerdeGlyphErr::StructUnnamedFields),
          Some(field_name) => {
            let ds = PassthroughDeserializer::Str(field_name);
            let value = seed.deserialize(ds)?;
            Ok(Some(value))
          },
        }
      },
    }
  }

  fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
  where
    V: DeserializeSeed<'de>,
  {
    if let Some(glyph) = self.value.take() {
      let gs = GlyphDeserializer(glyph);
      let value = seed.deserialize(gs)?;
      Ok(value)
    } else {
      Err(SerdeGlyphErr::StructFieldValueMissing)
    }
  }
}

struct ObjEnumAccess<'de>(ObjGlyph<ParsedGlyph<'de>>);

impl<'de> EnumAccess<'de> for ObjEnumAccess<'de> {
  type Error = SerdeGlyphErr;
  type Variant = Self;

  fn variant_seed<V>(
    self,
    seed: V,
  ) -> Result<(V::Value, Self::Variant), Self::Error>
  where
    V: DeserializeSeed<'de>,
  {
    let variant = self
      .0
      .variant_name_parsed()
      .ok_or(SerdeGlyphErr::VariantNameMissing)?;
    let variant_ds = PassthroughDeserializer::Str(variant);
    let variant = seed.deserialize(variant_ds)?;
    Ok((variant, self))
  }
}

impl<'de> VariantAccess<'de> for ObjEnumAccess<'de> {
  type Error = SerdeGlyphErr;

  fn unit_variant(self) -> Result<(), Self::Error> {
    if self.0.len() == 0 {
      Ok(())
    } else {
      Err(SerdeGlyphErr::UnexpectedFields)
    }
  }

  fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
  where
    T: DeserializeSeed<'de>,
  {
    if self.0.len() != 1 {
      Err(SerdeGlyphErr::UnexpectedFields)
    } else {
      let (_field_name, glyph) = self.0.nth_parse(0)?;
      let ds = GlyphDeserializer(glyph);
      seed.deserialize(ds)
    }
  }

  fn tuple_variant<V>(
    self,
    _len: usize,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    if self.0.has_field_names() {
      Err(SerdeGlyphErr::TupleNamedFields)
    } else {
      let mut iter =
        self.0.fields_iter_parse().map(|(_field_name, field)| field);
      let ds = IterSeqDeserializer(&mut iter);
      visitor.visit_seq(ds)
    }
  }

  fn struct_variant<V>(
    self,
    _fields: &'static [&'static str],
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    if !self.0.has_field_names() {
      Err(SerdeGlyphErr::StructUnnamedFields)
    } else {
      let mut iter = self.0.fields_iter_parse();
      let ds = StructAccess {
        it:    &mut iter,
        value: None,
      };
      visitor.visit_map(ds)
    }
  }
}

enum PassthroughDeserializer<'de> {
  Bool(bool),
  I8(i8),
  I16(i16),
  I32(i32),
  I64(i64),
  I128(i128),
  U8(u8),
  U16(u16),
  U32(u32),
  U64(u64),
  U128(u128),
  F32(f32),
  F64(f64),
  Str(&'de str),
}

impl<'de> PassthroughDeserializer<'de> {
  fn numbers<V>(self, visitor: V) -> Result<V::Value, SerdeGlyphErr>
  where
    V: Visitor<'de>,
  {
    match self {
      PassthroughDeserializer::Bool(v) => visitor.visit_bool(v),
      PassthroughDeserializer::I8(v) => visitor.visit_i8(v),
      PassthroughDeserializer::I16(v) => visitor.visit_i16(v),
      PassthroughDeserializer::I32(v) => visitor.visit_i32(v),
      PassthroughDeserializer::I64(v) => visitor.visit_i64(v),
      PassthroughDeserializer::I128(v) => visitor.visit_i128(v),
      PassthroughDeserializer::U8(v) => visitor.visit_u8(v),
      PassthroughDeserializer::U16(v) => visitor.visit_u16(v),
      PassthroughDeserializer::U32(v) => visitor.visit_u32(v),
      PassthroughDeserializer::U64(v) => visitor.visit_u64(v),
      PassthroughDeserializer::U128(v) => visitor.visit_u128(v),
      PassthroughDeserializer::F32(v) => visitor.visit_f32(v),
      PassthroughDeserializer::F64(v) => visitor.visit_f64(v),
      _ => Err(SerdeGlyphErr::Unreachable),
    }
  }

  fn strings<V>(self, visitor: V) -> Result<V::Value, SerdeGlyphErr>
  where
    V: Visitor<'de>,
  {
    match self {
      PassthroughDeserializer::Str(v) => visitor.visit_str(v),
      _ => Err(SerdeGlyphErr::Unreachable),
    }
  }
}

impl<'de> Deserializer<'de> for PassthroughDeserializer<'de> {
  type Error = SerdeGlyphErr;

  fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.numbers(visitor)
  }

  fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.strings(visitor)
  }

  fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.strings(visitor)
  }

  fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.strings(visitor)
  }

  fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.strings(visitor)
  }

  fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_unit_struct<V>(
    self,
    _name: &'static str,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_newtype_struct<V>(
    self,
    _name: &'static str,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_tuple<V>(
    self,
    _len: usize,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_tuple_struct<V>(
    self,
    _name: &'static str,
    _len: usize,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_struct<V>(
    self,
    _name: &'static str,
    _fields: &'static [&'static str],
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_enum<V>(
    self,
    _name: &'static str,
    _variants: &'static [&'static str],
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }

  fn deserialize_identifier<V>(
    self,
    visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    self.strings(visitor)
  }

  fn deserialize_ignored_any<V>(
    self,
    _visitor: V,
  ) -> Result<V::Value, Self::Error>
  where
    V: Visitor<'de>,
  {
    Err(SerdeGlyphErr::Unreachable)
  }
}
