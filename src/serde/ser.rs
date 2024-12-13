use crate::{
  collections::{
    MapGlyphLenCalc, MapGlyphSerializer, TupleGlyphLenCalc,
    TupleGlyphSerializer, VecGlyphLenCalc, VecGlyphSerializer,
  },
  serde::SerdeGlyphErr,
  structured::{ObjGlyphLenCalc, ObjGlyphSerializer},
  BoxGlyph, GlyphErr, ToGlyph,
};
use serde::{
  ser::{
    SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant,
    SerializeTuple, SerializeTupleStruct, SerializeTupleVariant,
  },
  Serialize, Serializer,
};

/// Serializes a type that implements [`Serialize`] into a glyph contained
/// in a heap-allocated buffer of the appropriate size.
///
/// For details regarding the encoding, see the documentation for
/// [`glyph_serde_serialize()`].
pub fn glyph_new_serde<T>(value: &T) -> Result<BoxGlyph, SerdeGlyphErr>
where
  T: Serialize,
{
  let glyph_len = value.serialize(GlyphLenCalc)?;
  let mut buffer = BoxGlyph::new_buffer(glyph_len)?;
  let mut cursor = 0;
  let gs = GlyphSerializer {
    target: buffer.as_mut(),
    cursor: &mut cursor,
  };
  value.serialize(gs)?;
  let glyph = BoxGlyph::try_from(buffer)?;
  Ok(glyph)
}

/// Serializes a type that implements [`Serialize`] into a glyph.
///
/// Parameters:
///
/// - `target`: The byte buffer into which the glyph will be serialized.  It
///   must be of sufficient length to contain the glyph, which will start at
///   the provided cursor position.  Note that this size can be determined by
///   calling [`glyph_serde_length()`].
/// - `cursor`: A cursor into the target byte buffer.  Upon return, its value
///   should be to the byte immediately following the encoded glyph.
///
/// Types are serialized as follows (which also corresponds to how these types
/// are deserialized):
///
/// - _Numeric Primitives_.  Any integer type that is 32 bits or less are
///   encoded as a [`U32Glyph`] or [`I32Glyph`].  Other primitives are encoded
///   as their more specific types (e.g., [`F64Glyph`], [`U128Glyph`].
/// - _Strings_. Encoded as [`StringGlyph`].  Currently only UTF-8 is
///   supported.
/// - _Options_. `None` is encoded as a [`NothingGlyph`].  `Some(T)` is encoded
///   as a `T`.
/// - _Sequences_.  All sequences are encoded as [`VecGlyph`].  Specialized
///   sequences of a single primitive type are not yet supported, but this may
///   be possible in a future revision.
/// - _Tuples_.  Serialized as [`TupleGlyph`]s.
/// - _Maps_.  Serialized as [`MapGlyph`]s.
/// - _Structs_.  Serialized as [`ObjGlyph`]s with corresponding type names.
///   Unit structs have no fields, tuple structs have unnamed fields, and
///   regular structs have named fields.  Newtype structs are serialized
///   transparently, e.g., `struct T(U)` will be serialized as if it were of
///   type `U`.
/// - _Enums_.  Serialized like structs, except that (1) the target `ObjGlyph`
///   will also contain the variant name and (2) newtype variants are serialized
///   as tuple variants with a single item.
pub fn glyph_serde_serialize<T>(
  value: &T,
  target: &mut [u8],
  cursor: &mut usize,
) -> Result<(), SerdeGlyphErr>
where
  T: Serialize,
{
  value.serialize(GlyphSerializer { target, cursor })
}

/// Calculates the length of the buffer necessary to serialize a type as a
/// glyph with `serde`.
pub fn glyph_serde_length<T>(value: &T) -> Result<usize, SerdeGlyphErr>
where
  T: Serialize,
{
  value.serialize(GlyphLenCalc)
}

/// Allows internal GLIFS serializers that expect `ToGlyph` objects to serialize
/// types that implement [`Serialize`].
///
/// This is primarily useful when serializing e.g., [`VecGlyphs`], as it allows
/// us to use the same GLIFS native serializers rather than writing and
/// maintaining a parallel implementation here.
struct ToGlyphSerializer<'a, T>(&'a T)
where
  T: ?Sized;

impl<'a, T> ToGlyph for ToGlyphSerializer<'a, T>
where
  T: ?Sized + Serialize,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.0.serialize(GlyphSerializer { target, cursor })?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    self.0.serialize(GlyphLenCalc).unwrap_or(0)
  }
}

/// Main GLIFS [`Serializer`] type.
struct GlyphSerializer<'a> {
  target: &'a mut [u8],
  cursor: &'a mut usize,
}

impl<'a> Serializer for GlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();
  type SerializeMap = MapGlyphSerializer<'a>;
  type SerializeSeq = VecGlyphSerializer<'a>;
  type SerializeStruct = ObjGlyphSerializer<'a>;
  type SerializeStructVariant = ObjGlyphSerializer<'a>;
  type SerializeTuple = TupleGlyphSerializer<'a>;
  type SerializeTupleStruct = ObjGlyphSerializer<'a>;
  type SerializeTupleVariant = ObjGlyphSerializer<'a>;

  fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
    v.glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
    ().glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    // Pass-through
    value.serialize(self)
  }

  fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
    ().glyph_encode(self.target, self.cursor)?;
    Ok(())
  }

  fn serialize_unit_struct(
    self,
    name: &'static str,
  ) -> Result<Self::Ok, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      None,
      false,
      false,
      0,
      self.target,
      self.cursor,
    )?;
    ogs.finish()?;
    Ok(())
  }

  fn serialize_unit_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
  ) -> Result<Self::Ok, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      Some(variant),
      false,
      false,
      0,
      self.target,
      self.cursor,
    )?;
    ogs.finish()?;
    Ok(())
  }

  fn serialize_newtype_struct<T>(
    self,
    _name: &'static str,
    value: &T,
  ) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    // Pass-through
    value.serialize(self)
  }

  fn serialize_newtype_variant<T>(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    value: &T,
  ) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let mut ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      Some(variant),
      false,
      false,
      1,
      self.target,
      self.cursor,
    )?;
    ogs.add_field(None, &ToGlyphSerializer(value))?;
    ogs.finish()?;
    Ok(())
  }

  fn serialize_seq(
    self,
    len: Option<usize>,
  ) -> Result<Self::SerializeSeq, Self::Error> {
    match len {
      None => Err(SerdeGlyphErr::SeqLengthRequired),
      Some(len) => {
        let vgs = VecGlyphSerializer::new(len, self.target, self.cursor)?;
        Ok(vgs)
      },
    }
  }

  fn serialize_tuple(
    self,
    _len: usize,
  ) -> Result<Self::SerializeTuple, Self::Error> {
    let tgs = TupleGlyphSerializer::new(self.target, self.cursor)?;
    Ok(tgs)
  }

  fn serialize_tuple_struct(
    self,
    name: &'static str,
    len: usize,
  ) -> Result<Self::SerializeTupleStruct, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      None,
      false,
      false,
      len,
      self.target,
      self.cursor,
    )?;
    Ok(ogs)
  }

  fn serialize_tuple_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    len: usize,
  ) -> Result<Self::SerializeTupleVariant, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      Some(variant),
      false,
      false,
      len,
      self.target,
      self.cursor,
    )?;
    Ok(ogs)
  }

  fn serialize_map(
    self,
    len: Option<usize>,
  ) -> Result<Self::SerializeMap, Self::Error> {
    match len {
      None => Err(SerdeGlyphErr::MapLengthRequired),
      Some(len) => {
        let mgs = MapGlyphSerializer::new(len, self.target, self.cursor)?;
        Ok(mgs)
      },
    }
  }

  fn serialize_struct(
    self,
    name: &'static str,
    len: usize,
  ) -> Result<Self::SerializeStruct, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      None,
      true,
      false,
      len,
      self.target,
      self.cursor,
    )?;
    Ok(ogs)
  }

  fn serialize_struct_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    len: usize,
  ) -> Result<Self::SerializeStructVariant, Self::Error> {
    let ogs = ObjGlyphSerializer::new(
      None,
      Some(name),
      None,
      Some(variant),
      true,
      false,
      len,
      self.target,
      self.cursor,
    )?;
    Ok(ogs)
  }
}

impl<'a> SerializeTuple for TupleGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_item(&ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish()?)
  }
}

impl<'a> SerializeSeq for VecGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_field(&ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish()?)
  }
}

impl<'a> SerializeMap for MapGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_key(&ToGlyphSerializer(key))?;
    Ok(())
  }

  fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_value(&ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    self.finish()?;
    Ok(())
  }
}

impl<'a> SerializeStruct for ObjGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_field<T>(
    &mut self,
    key: &'static str,
    value: &T,
  ) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_field(Some(key), &ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    self.finish()?;
    Ok(())
  }
}

impl<'a> SerializeTupleStruct for ObjGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_field(None, &ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    self.finish()?;
    Ok(())
  }
}

impl<'a> SerializeStructVariant for ObjGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_field<T>(
    &mut self,
    key: &'static str,
    value: &T,
  ) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_field(Some(key), &ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    self.finish()?;
    Ok(())
  }
}

impl<'a> SerializeTupleVariant for ObjGlyphSerializer<'a> {
  type Error = SerdeGlyphErr;
  type Ok = ();

  fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    self.add_field(None, &ToGlyphSerializer(value))?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    self.finish()?;
    Ok(())
  }
}

/// Type used for `serde` to calculate the length of glyphs before
/// serialization.
struct GlyphLenCalc;

impl Serializer for GlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;
  type SerializeMap = MapGlyphLenCalc;
  type SerializeSeq = VecGlyphLenCalc;
  type SerializeStruct = ObjGlyphLenCalc;
  type SerializeStructVariant = ObjGlyphLenCalc;
  type SerializeTuple = TupleGlyphLenCalc;
  type SerializeTupleStruct = ObjGlyphLenCalc;
  type SerializeTupleVariant = ObjGlyphLenCalc;

  fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
    Ok(v.glyph_len())
  }

  fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
    Ok(().glyph_len())
  }

  fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    value.serialize(GlyphLenCalc)
  }

  fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
    Ok(().glyph_len())
  }

  fn serialize_unit_struct(
    self,
    name: &'static str,
  ) -> Result<Self::Ok, Self::Error> {
    // Unit structs are stored as ObjGlyphs, with a labeled type name and no
    // fields.
    let obj_len = ObjGlyphLenCalc::new(false, Some(name), None, false)?;
    Ok(obj_len.finish())
  }

  fn serialize_unit_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
  ) -> Result<Self::Ok, Self::Error> {
    // Unit variants are stored as ObjGlyphs, with a labeled type name, a
    // labeled variant name, and no fields.
    let obj_len =
      ObjGlyphLenCalc::new(false, Some(name), Some(variant), false)?;
    Ok(obj_len.finish())
  }

  fn serialize_newtype_struct<T>(
    self,
    _name: &'static str,
    value: &T,
  ) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    // Newtype Structs (e.g., `struct NewType(OldType)`) are just passthroughs
    //   to OldType.
    value.serialize(self)
  }

  fn serialize_newtype_variant<T>(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    value: &T,
  ) -> Result<Self::Ok, Self::Error>
  where
    T: ?Sized + Serialize,
  {
    // Newtype Variants (e.g., `NewType::Variant(OldType)`) are stored as
    // ObjGlyphs, with a labeled type name, a labeled and one  unnamed field.
    let mut obj_len =
      ObjGlyphLenCalc::new(false, Some(name), Some(variant), false)?;
    let field_len = value.serialize(GlyphLenCalc)?;
    obj_len.add_field(None, field_len)?;
    Ok(obj_len.finish())
  }

  fn serialize_seq(
    self,
    _len: Option<usize>,
  ) -> Result<Self::SerializeSeq, Self::Error> {
    Ok(VecGlyphLenCalc::default())
  }

  fn serialize_tuple(
    self,
    _len: usize,
  ) -> Result<Self::SerializeTuple, Self::Error> {
    Ok(TupleGlyphLenCalc::default())
  }

  fn serialize_tuple_struct(
    self,
    name: &'static str,
    _len: usize,
  ) -> Result<Self::SerializeTupleStruct, Self::Error> {
    // Tuple structs are just ObjGlyphs with unnamed fields.
    let obj_len = ObjGlyphLenCalc::new(false, Some(name), None, false)?;
    Ok(obj_len)
  }

  fn serialize_tuple_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    _len: usize,
  ) -> Result<Self::SerializeTupleVariant, Self::Error> {
    let obj_len =
      ObjGlyphLenCalc::new(false, Some(name), Some(variant), false)?;
    Ok(obj_len)
  }

  fn serialize_map(
    self,
    _len: Option<usize>,
  ) -> Result<Self::SerializeMap, Self::Error> {
    Ok(MapGlyphLenCalc::default())
  }

  fn serialize_struct(
    self,
    name: &'static str,
    _len: usize,
  ) -> Result<Self::SerializeStruct, Self::Error> {
    let obj_len = ObjGlyphLenCalc::new(false, Some(name), None, false)?;
    Ok(obj_len)
  }

  fn serialize_struct_variant(
    self,
    name: &'static str,
    _variant_index: u32,
    variant: &'static str,
    _len: usize,
  ) -> Result<Self::SerializeStructVariant, Self::Error> {
    let obj_len =
      ObjGlyphLenCalc::new(false, Some(name), Some(variant), false)?;
    Ok(obj_len)
  }
}

impl SerializeSeq for VecGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let item_len = value.serialize(GlyphLenCalc)?;
    self.add_item(item_len);
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeTuple for TupleGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let item_len = value.serialize(GlyphLenCalc)?;
    self.add_item(item_len);
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeStruct for ObjGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_field<T>(
    &mut self,
    key: &'static str,
    value: &T,
  ) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let field_len = value.serialize(GlyphLenCalc)?;
    self.add_field(Some(key), field_len)?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeTupleStruct for ObjGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let field_len = value.serialize(GlyphLenCalc)?;
    self.add_field(None, field_len)?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeStructVariant for ObjGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_field<T>(
    &mut self,
    key: &'static str,
    value: &T,
  ) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let field_len = value.serialize(GlyphLenCalc)?;
    self.add_field(Some(key), field_len)?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeTupleVariant for ObjGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let field_len = value.serialize(GlyphLenCalc)?;
    self.add_field(None, field_len)?;
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}

impl SerializeMap for MapGlyphLenCalc {
  type Error = SerdeGlyphErr;
  type Ok = usize;

  fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let key_len = key.serialize(GlyphLenCalc)?;
    self.add_key(key_len);
    Ok(())
  }

  fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
  where
    T: ?Sized + Serialize,
  {
    let value_len = value.serialize(GlyphLenCalc)?;
    self.add_value(value_len);
    Ok(())
  }

  fn end(self) -> Result<Self::Ok, Self::Error> {
    Ok(self.finish())
  }
}
