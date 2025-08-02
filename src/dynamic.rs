use crate::{
  basic::{
    BitVecGlyph, BoolGlyph, CharGlyph, FloatGlyph, IntGlyph, StringGlyph,
    UIntGlyph, UnitGlyph,
  },
  collections::{BasicVecGlyph, MapGlyph, TupleGlyph, VecGlyph},
  crypto::{HashGlyph, PasswordGlyph},
  misc::{DateTimeGlyph, UuidGlyph},
  structured::{DocGlyph, ObjGlyph},
  EncodedGlyph, FromGlyph, Glyph, GlyphDecodeErr, GlyphErr, GlyphSorting,
  GlyphType,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};
use std::ops::Deref;

pub enum DynGlyph<G: Deref<Target = Glyph>> {
  //=== Primitives
  Unit(UnitGlyph<G>),
  Bool(BoolGlyph<G>),
  Int(IntGlyph<G>),
  UInt(UIntGlyph<G>),
  Float(FloatGlyph<G>),

  //=== Collections
  Tuple(TupleGlyph<G>),
  Vec(VecGlyph<G>),
  BitVec(BitVecGlyph<G>),
  BasicVec(BasicVecGlyph<G>),
  Map(MapGlyph<G>),
  Obj(ObjGlyph<G>),
  Doc(DocGlyph<G>),

  //=== Language
  String(StringGlyph<G>),
  Char(CharGlyph<G>),

  //=== Other
  DateTime(DateTimeGlyph<G>),
  UUID(UuidGlyph<G>),

  // === Crypto
  // TODO: Convert this to a generic type, get rid of additional generic
  CryptoHash(HashGlyph<G>),
  EncryptedPassword(PasswordGlyph<G>),
  // PublicKey,
  // PrivateKey,
  // KeyPair,
  // Signature,
  // SignedExtent,
  // SignedGlyph,
  // EncryptedExtent,
  // EncryptedGlyph,
  // CiphertextMetadata,

  //=== Fallback
  UnknownType(G),
  DecodeErr(GlyphErr, G),
}

impl<G: Deref<Target = Glyph>> DynGlyph<G> {
  pub fn new(src: G) -> Self {
    let result = match src.glyph_type() {
      GlyphType::Unit => UnitGlyph::from_glyph(src).map(|g| DynGlyph::Unit(g)),
      GlyphType::Bool => BoolGlyph::from_glyph(src).map(|g| DynGlyph::Bool(g)),
      GlyphType::SignedInt => {
        IntGlyph::from_glyph(src).map(|g| DynGlyph::Int(g))
      },
      GlyphType::UnsignedInt => {
        UIntGlyph::from_glyph(src).map(|g| DynGlyph::UInt(g))
      },
      GlyphType::Float => {
        FloatGlyph::from_glyph(src).map(|g| DynGlyph::Float(g))
      },
      GlyphType::Tuple => {
        TupleGlyph::from_glyph(src).map(|g| DynGlyph::Tuple(g))
      },
      GlyphType::Vec => VecGlyph::from_glyph(src).map(|g| DynGlyph::Vec(g)),
      GlyphType::VecBasic => {
        BasicVecGlyph::from_glyph(src).map(|g| DynGlyph::BasicVec(g))
      },
      GlyphType::VecBool => {
        BitVecGlyph::from_glyph(src).map(|g| DynGlyph::BitVec(g))
      },
      GlyphType::Map => MapGlyph::from_glyph(src).map(|g| DynGlyph::Map(g)),
      GlyphType::Object => ObjGlyph::from_glyph(src).map(|g| DynGlyph::Obj(g)),
      GlyphType::Document => {
        DocGlyph::from_glyph(src).map(|g| DynGlyph::Doc(g))
      },
      GlyphType::String => {
        StringGlyph::from_glyph(src).map(|g| DynGlyph::String(g))
      },
      GlyphType::UnicodeChar => {
        CharGlyph::from_glyph(src).map(|g| DynGlyph::Char(g))
      },
      GlyphType::UUID => UuidGlyph::from_glyph(src).map(|g| DynGlyph::UUID(g)),
      GlyphType::CryptoHash => {
        HashGlyph::from_glyph(src).map(|g| DynGlyph::CryptoHash(g))
      },
      GlyphType::PasswordHash => {
        PasswordGlyph::from_glyph(src).map(|g| DynGlyph::EncryptedPassword(g))
      },

      //FIXME
      //
      // GlyphType::PublicKey => {
      //   PublicKeyGlyph::from_glyph(src).map(|g| DynGlyph::PublicKey(g))
      // },
      // GlyphType::PrivateKey => {
      //   PrivateKeyGlyph::from_glyph(src).map(|g| DynGlyph::PrivateKey(g))
      // },
      // GlyphType::KeyPair => {
      //   KeyPairGlyph::from_glyph(src).map(|g| DynGlyph::KeyPair(g))
      // },
      // GlyphType::Signature => {
      //   SignatureGlyph::from_glyph(src).map(|g| DynGlyph::Signature(g))
      // },
      // GlyphType::SignedExtent => {
      //   SignedExtentGlyph::from_glyph(src).map(|g| DynGlyph::SignedExtent(g))
      // },
      // GlyphType::SignedGlyph => {
      //   SignedGlyph::from_glyph(src).map(|g| DynGlyph::SignedGlyph(g))
      // },
      // GlyphType::EncryptedExtent => {
      //   EncryptedExtentGlyph::from_glyph(src).map(|g| DynGlyph::EncryptedExtent(g))
      // },
      // GlyphType::EncryptedGlyph => {
      //   EncryptedGlyph::from_glyph(src).map(|g| DynGlyph::EncryptedGlyph(g))
      // },
      // GlyphType::CiphertextMetadata => {
      //   CiphertextMetadataGlyph::from_glyph(src).map(|g| DynGlyph::CiphertextMetadata(g))
      // },
      // GlyphType::GlifsTxLog => {
      //   GlifsTxLogGlyph::from_glyph(src).map(|g| DynGlyph::GlifsTxLog(g))
      // },
      // GlyphType::Unknown => {},
      _ => todo!(),
    };

    result.unwrap_or_else(|fge| {
      let (glyph, err) = fge.into_parts();
      DynGlyph::DecodeErr(err, glyph)
    })
  }
}

impl<G: Deref<Target = Glyph>> Debug for DynGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match self {
      DynGlyph::Unit(g) => Debug::fmt(g, f)?,
      DynGlyph::Bool(g) => Debug::fmt(g, f)?,
      DynGlyph::Int(g) => Debug::fmt(g, f)?,
      DynGlyph::UInt(g) => Debug::fmt(g, f)?,
      DynGlyph::Float(g) => Debug::fmt(g, f)?,
      DynGlyph::Tuple(g) => Debug::fmt(g, f)?,
      DynGlyph::Vec(g) => Debug::fmt(g, f)?,
      DynGlyph::BitVec(g) => Debug::fmt(g, f)?,
      DynGlyph::BasicVec(g) => Debug::fmt(g, f)?,
      DynGlyph::Map(g) => Debug::fmt(g, f)?,
      DynGlyph::Obj(g) => Debug::fmt(g, f)?,
      DynGlyph::Doc(g) => Debug::fmt(g, f)?,
      DynGlyph::String(g) => Debug::fmt(g, f)?,
      DynGlyph::Char(g) => Debug::fmt(g, f)?,
      DynGlyph::DateTime(g) => Debug::fmt(g, f)?,
      DynGlyph::UUID(g) => Debug::fmt(g, f)?,
      DynGlyph::CryptoHash(g) => Debug::fmt(g, f)?,
      DynGlyph::EncryptedPassword(g) => Debug::fmt(g, f)?,
      DynGlyph::UnknownType(g) => {
        write!(f, "UnknownGlyphType({:?})", &g.header().glyph_type())?;
      },
      DynGlyph::DecodeErr(err, g) => {
        let mut df = f.debug_struct("DecodeErr");
        df.field("glyph", &g.deref());
        df.field("error", err);
        df.finish()?;
      },
    }
    Ok(())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for DynGlyph<G> {
  fn into_inner(self) -> G {
    match self {
      DynGlyph::Unit(g) => g.into_inner(),
      DynGlyph::Bool(g) => g.into_inner(),
      DynGlyph::Int(g) => g.into_inner(),
      DynGlyph::UInt(g) => g.into_inner(),
      DynGlyph::Float(g) => g.into_inner(),
      DynGlyph::BitVec(g) => g.into_inner(),
      DynGlyph::String(g) => g.into_inner(),
      DynGlyph::Char(g) => g.into_inner(),
      DynGlyph::Tuple(g) => g.into_inner(),
      DynGlyph::Vec(g) => g.into_inner(),
      DynGlyph::BasicVec(g) => g.into_inner(),
      DynGlyph::Map(g) => g.into_inner(),
      DynGlyph::Obj(g) => g.into_inner(),
      DynGlyph::Doc(g) => g.into_inner(),
      DynGlyph::DateTime(g) => g.into_inner(),
      DynGlyph::UUID(g) => g.into_inner(),
      DynGlyph::CryptoHash(g) => g.into_inner(),
      DynGlyph::EncryptedPassword(g) => g.into_inner(),
      DynGlyph::UnknownType(g) => g,
      DynGlyph::DecodeErr(_err, g) => g,
    }
  }

  fn glyph(&self) -> &Glyph {
    match self {
      DynGlyph::Unit(eg) => eg.glyph(),
      DynGlyph::Bool(eg) => eg.glyph(),
      DynGlyph::Int(eg) => eg.glyph(),
      DynGlyph::UInt(eg) => eg.glyph(),
      DynGlyph::Float(eg) => eg.glyph(),
      DynGlyph::Tuple(eg) => eg.glyph(),
      DynGlyph::Vec(eg) => eg.glyph(),
      DynGlyph::BitVec(eg) => eg.glyph(),
      DynGlyph::BasicVec(eg) => eg.glyph(),
      DynGlyph::Map(eg) => eg.glyph(),
      DynGlyph::Obj(eg) => eg.glyph(),
      DynGlyph::Doc(eg) => eg.glyph(),
      DynGlyph::String(eg) => eg.glyph(),
      DynGlyph::Char(eg) => eg.glyph(),
      DynGlyph::DateTime(eg) => eg.glyph(),
      DynGlyph::UUID(eg) => eg.glyph(),
      DynGlyph::CryptoHash(eg) => eg.glyph(),
      DynGlyph::EncryptedPassword(eg) => eg.glyph(),
      DynGlyph::UnknownType(g) => g.deref(),
      DynGlyph::DecodeErr(_, g) => g.deref(),
    }
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    // Type-based classification.

    match (self, other) {
      //=== Same Type Comparisons
      (DynGlyph::Unit(a), DynGlyph::Unit(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Bool(a), DynGlyph::Bool(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Int(a), DynGlyph::Int(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::UInt(a), DynGlyph::UInt(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Float(a), DynGlyph::Float(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Tuple(a), DynGlyph::Tuple(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Vec(a), DynGlyph::Vec(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::BitVec(a), DynGlyph::BitVec(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::BasicVec(a), DynGlyph::BasicVec(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Map(a), DynGlyph::Map(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Obj(a), DynGlyph::Obj(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Doc(a), DynGlyph::Doc(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::String(a), DynGlyph::String(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Char(a), DynGlyph::Char(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::DateTime(a), DynGlyph::DateTime(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::UUID(a), DynGlyph::UUID(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::UnknownType(a), DynGlyph::UnknownType(b)) => a
        .glyph_type()
        .cmp(&b.glyph_type())
        .then_with(|| a.content().cmp(b.content())),

      //=== Inter Type Comparisons
      (DynGlyph::UInt(a), DynGlyph::Int(b)) => {
        // TODO: Comparisons using big integers require allocation
        a.get_big_int().cmp(&b.get_big_int())
      },
      (DynGlyph::Int(a), DynGlyph::UInt(b)) => {
        // TODO: Comparisons using big integers require allocation
        a.get_big_int().cmp(&b.get_big_int())
      },
      //=== Comparisons with floats; convert both to float ===//
      (DynGlyph::Float(_a), DynGlyph::Int(_b)) => {
        todo!("Integer / Float cross-type comparison")
      },
      (DynGlyph::Int(_a), DynGlyph::Float(_b)) => {
        todo!("Integer / Float cross-type comparison")
      },
      (DynGlyph::Float(_a), DynGlyph::UInt(_b)) => {
        todo!("Integer / Float cross-type comparison")
      },
      (DynGlyph::UInt(_a), DynGlyph::Float(_b)) => {
        todo!("Integer / Float cross-type comparison")
      },

      //=== Error Comparisons: Errors always sort last. ===/
      (DynGlyph::DecodeErr(_, a), DynGlyph::DecodeErr(_, b)) => a
        .glyph_type()
        .cmp(&b.glyph_type())
        .then_with(|| a.content().cmp(b.content())),
      (DynGlyph::DecodeErr(_, _), _) => Ordering::Greater,
      (_, DynGlyph::DecodeErr(_, _)) => Ordering::Less,

      //=== Residual: Mostly unspecified cross-type comparisons ===/
      (a, b) => {
        let a = a.glyph();
        let b = b.glyph();
        a.glyph_type()
          .cmp(&b.glyph_type())
          .then_with(|| a.content().cmp(b.content()))
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for DynGlyph<G> {}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for DynGlyph<G> {
  fn from_glyph(src: G) -> Result<Self, GlyphDecodeErr<G>> {
    Ok(DynGlyph::new(src))
  }
}

impl<G: Deref<Target = Glyph>> Ord for DynGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for DynGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for DynGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    crypto::{CryptographicHash, GlyphHash, Password},
  };
  use rand::thread_rng;
  use std::{dbg, vec};

  #[test]
  fn dyn_glyph_debug() {
    let unit_glyph = Glyph::new(&()).unwrap();
    let unit_dyn = DynGlyph::from_glyph(unit_glyph).unwrap();
    dbg!(&unit_dyn);

    let bool_glyph = Glyph::new(&true).unwrap();
    let bool_dyn = DynGlyph::from_glyph(bool_glyph).unwrap();
    dbg!(&bool_dyn);

    let int_glyph = Glyph::new(&-123).unwrap();
    let int_dyn = DynGlyph::from_glyph(int_glyph).unwrap();
    dbg!(&int_dyn);

    let uint_glyph = Glyph::new(&123u128).unwrap();
    let uint_dyn = DynGlyph::from_glyph(uint_glyph).unwrap();
    dbg!(&uint_dyn);

    let float_glyph = Glyph::new(&123.456f64).unwrap();
    let float_dyn = DynGlyph::from_glyph(float_glyph).unwrap();
    dbg!(&float_dyn);

    let tuple_glyph = Glyph::new(&(123, 456)).unwrap();
    let tuple_dyn = DynGlyph::from_glyph(tuple_glyph).unwrap();
    dbg!(&tuple_dyn);

    let vec_glyph = Glyph::new(&vec!["foo", "bar", "baz"]).unwrap();
    let vec_dyn = DynGlyph::from_glyph(vec_glyph).unwrap();
    dbg!(&vec_dyn);

    let basic_vec_glyph = Glyph::new(&vec![123, 456, 7890]).unwrap();
    let basic_vec_dyn = DynGlyph::from_glyph(basic_vec_glyph).unwrap();
    dbg!(&basic_vec_dyn);

    let map_glyph = Glyph::new(&std::collections::BTreeMap::from([
      ("key1", "value1"),
      ("key2", "value2"),
      ("key3", "value3"),
    ]))
    .unwrap();
    let map_dyn = DynGlyph::from_glyph(map_glyph).unwrap();
    dbg!(&map_dyn);


    // let obj = TestStruct { age: 34, name: String::from("Elara") };
    // let obj_glyph = Glyph::new(&obj).unwrap();
    // let obj_dyn = DynGlyph::from_glyph(obj_glyph).unwrap();
    // dbg!(&obj_dyn);

    let str_glyph = Glyph::new(&"Hello World!").unwrap();
    let str_dyn = DynGlyph::from_glyph(str_glyph).unwrap();
    dbg!(&str_dyn);

    let char_glyph = Glyph::new(&'a').unwrap();
    let char_dyn = DynGlyph::from_glyph(char_glyph).unwrap();
    dbg!(&char_dyn);

    let uuid_glyph = Glyph::new(&uuid::Uuid::new_v4()).unwrap();
    let uuid_dyn = DynGlyph::from_glyph(uuid_glyph).unwrap();
    dbg!(&uuid_dyn);

    let hash_glyph = Glyph::new(&GlyphHash::new(b"glifs")).unwrap();
    let hash_dyn = DynGlyph::from_glyph(hash_glyph).unwrap();
    dbg!(&hash_dyn);

    let pw = Password::new_argon2id(b"hunter2", thread_rng()).unwrap();
    let pw_glyph = Glyph::new(&pw).unwrap();
    let pw_dyn = DynGlyph::from_glyph(pw_glyph).unwrap();
    dbg!(&pw_dyn);
  }
}
