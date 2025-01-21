use crate::{
  basic::{
    BitVecGlyph, BooleanGlyph, CharGlyph, FloatGlyph, IntGlyph, StringGlyph,
    UIntGlyph, UnitGlyph,
  },
  collections::{BasicVecGlyph, MapGlyph, TupleGlyph, VecGlyph},
  crypto::{HashGlyph, PasswordGlyph},
  misc::UuidGlyph,
  structured::{DocGlyph, ObjGlyph},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphSorting,
  GlyphType, ParsedGlyph,
};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
};

pub enum DynGlyph<G: Glyph> {
  //=== Primitives
  Unit(UnitGlyph<G>),
  Bool(BooleanGlyph<G>),
  Int(IntGlyph<G>),
  UnsignedInt(UIntGlyph<G>),
  Float(FloatGlyph<G>),

  //=== Collections
  Tuple(TupleGlyph<G>),
  Vec(VecGlyph<G>),
  VecBool(BitVecGlyph<G>),
  VecBasic(BasicVecGlyph<G>),
  Map(MapGlyph<G>),
  Object(ObjGlyph<G>),
  Document(DocGlyph<G>),

  //=== Language
  String(StringGlyph<G>),
  Char(CharGlyph<G>),

  //=== Other
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

impl<G: Glyph> DynGlyph<G> {
  pub fn from_glyph_u(src: G) -> Self {
    let _result = match src.glyph_type() {
      GlyphType::Unit => UnitGlyph::from_glyph(src).map(|g| DynGlyph::Unit(g)),
      GlyphType::Bool => {
        BooleanGlyph::from_glyph(src).map(|g| DynGlyph::Bool(g))
      },
      GlyphType::SignedInt => {
        IntGlyph::from_glyph(src).map(|g| DynGlyph::Int(g))
      },
      GlyphType::UnsignedInt => {
        UIntGlyph::from_glyph(src).map(|g| DynGlyph::UnsignedInt(g))
      },
      GlyphType::Float => {
        FloatGlyph::from_glyph(src).map(|g| DynGlyph::Float(g))
      },
      GlyphType::Tuple => {
        TupleGlyph::from_glyph(src).map(|g| DynGlyph::Tuple(g))
      },
      GlyphType::Vec => VecGlyph::from_glyph(src).map(|g| DynGlyph::Vec(g)),
      GlyphType::VecBasic => {
        BasicVecGlyph::from_glyph(src).map(|g| DynGlyph::VecBasic(g))
      },
      GlyphType::VecBool => {
        BitVecGlyph::from_glyph(src).map(|g| DynGlyph::VecBool(g))
      },
      GlyphType::Map => MapGlyph::from_glyph(src).map(|g| DynGlyph::Map(g)),
      GlyphType::Object => {
        ObjGlyph::from_glyph(src).map(|g| DynGlyph::Object(g))
      },
      GlyphType::Document => {
        DocGlyph::from_glyph(src).map(|g| DynGlyph::Document(g))
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
      GlyphType::EncryptedPassword => {
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

    todo!()
  }
}

impl<G: Glyph> FromGlyph<G> for DynGlyph<G> {
  fn from_glyph(src: G) -> Result<Self, FromGlyphErr<G>> {
    Ok(DynGlyph::from_glyph_u(src))
  }
}

impl<G: Glyph> EncodedGlyph<G> for DynGlyph<G> {
  fn into_inner(self) -> G {
    match self {
      DynGlyph::Unit(g) => g.into_inner(),
      DynGlyph::Bool(g) => g.into_inner(),
      DynGlyph::Int(g) => g.into_inner(),
      DynGlyph::UnsignedInt(g) => g.into_inner(),
      DynGlyph::Float(g) => g.into_inner(),
      // DynGlyph::Tuple(g) => g.into_inner(),
      // DynGlyph::Vec(g) => g.into_inner(),
      DynGlyph::VecBool(g) => g.into_inner(),
      // DynGlyph::VecBasic(g) => g.into_inner(),
      // DynGlyph::Map(g) => g.into_inner(),
      // DynGlyph::Object(g) => g.into_inner(),
      // DynGlyph::Document(g) => g.into_inner(),
      DynGlyph::String(g) => g.into_inner(),
      DynGlyph::Char(g) => g.into_inner(),
      // DynGlyph::UUID(g) => g.into_inner(),
      // DynGlyph::CryptoHash(g) => g.into_inner(),
      // DynGlyph::EncryptedPassword(g) => g.into_inner(),
      DynGlyph::UnknownType(g) => g,
      DynGlyph::DecodeErr(_err, g) => g,
      _ => panic!(),
    }
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    match self {
      DynGlyph::Unit(eg) => eg.glyph(),
      DynGlyph::Bool(eg) => eg.glyph(),
      DynGlyph::Int(eg) => eg.glyph(),
      DynGlyph::UnsignedInt(eg) => eg.glyph(),
      DynGlyph::Float(eg) => eg.glyph(),
      // DynGlyph::Tuple(eg) => eg.glyph(),
      // DynGlyph::Vec(eg) => eg.glyph(),
      DynGlyph::VecBool(eg) => eg.glyph(),
      // DynGlyph::VecBasic(eg) => eg.glyph(),
      // DynGlyph::Map(eg) => eg.glyph(),
      // DynGlyph::Object(eg) => eg.glyph(),
      // DynGlyph::Document(eg) => eg.glyph(),
      DynGlyph::String(eg) => eg.glyph(),
      DynGlyph::Char(eg) => eg.glyph(),
      // DynGlyph::UUID(eg) => eg.glyph(),
      DynGlyph::UnknownType(g) => g.borrow(),
      _ => todo!(),
    }
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    // Type-based classification.

    match (self, other) {
      //=== Same Type Comparisons
      (DynGlyph::Unit(a), DynGlyph::Unit(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Bool(a), DynGlyph::Bool(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Int(a), DynGlyph::Int(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::UnsignedInt(a), DynGlyph::UnsignedInt(b)) => {
        a.glyph_ord(b, sorting)
      },
      (DynGlyph::Float(a), DynGlyph::Float(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::Tuple(a), DynGlyph::Tuple(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::Vec(a), DynGlyph::Vec(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::VecBool(a), DynGlyph::VecBool(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::VecBasic(a), DynGlyph::VecBasic(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::Map(a), DynGlyph::Map(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::Object(a), DynGlyph::Object(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::Document(a), DynGlyph::Document(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::String(a), DynGlyph::String(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::Char(a), DynGlyph::Char(b)) => a.glyph_ord(b, sorting),
      // (DynGlyph::UUID(a), DynGlyph::UUID(b)) => a.glyph_ord(b, sorting),
      (DynGlyph::UnknownType(a), DynGlyph::UnknownType(b)) => {
        // TypeID first, then content by bytes
        todo!()
      },

      //=== Inter Type Comparisons
      (DynGlyph::UnsignedInt(a), DynGlyph::Int(b)) => {
        if *b.get() < 0 {
          Ordering::Greater
        } else {
          let b = *b.get() as u128;
          a.get().cmp(&b)
        }
      },
      (DynGlyph::Int(a), DynGlyph::UnsignedInt(b)) => {
        if *a.get() < 0 {
          Ordering::Less
        } else {
          let a = *a.get() as u128;
          a.cmp(b.get())
        }
      },
      (DynGlyph::Float(_a), DynGlyph::Int(_b)) => {
        todo!()
      },
      (DynGlyph::Int(_a), DynGlyph::Float(_b)) => {
        todo!()
      },
      (DynGlyph::Float(_a), DynGlyph::UnsignedInt(_b)) => {
        todo!()
      },
      (DynGlyph::UnsignedInt(_a), DynGlyph::Float(_b)) => {
        todo!()
      },

      (_, _) => {
        todo!()
      },
    }
  }
}

impl<G: Glyph> PartialEq for DynGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    todo!()
  }
}

impl<G: Glyph> Eq for DynGlyph<G> {}

impl<G: Glyph> PartialOrd for DynGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    todo!()
  }
}

impl<G: Glyph> Ord for DynGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    todo!()
  }
}

impl<G: Glyph> Debug for DynGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    todo!()
  }
}
