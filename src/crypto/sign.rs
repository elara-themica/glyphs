//! Signing Keys and Signatures
//!
//! - [`Signature`]s are created by a [`SigningKey`], which is an `enum` over
//!   the known/supported cryptographic signature methods.
//! - The serialized version is a [`SignatureGlyph`].
//! - Signatures are calculated over the following bytes:
//!   - The little-endian `U16` identifying the reason for the signature
//!     (`reason_id`)
//!   - An additional `[u8; 14]` bytes holding reason specific data
//!     (essentially, this is a tagged union identified by `reason_id`)
//!   - The [`GlyphHash`] of the content this signature is signing.
//!   - An optional [`Glyph`] with more information on the signature not present
//!     in the 14 bytes referred to above.  (In an encoded glyph, the presence
//!     of this glyph will be indicated by a flag in the header).
//!   - A `[u8; 16]` proof-of-work nonce, described below.
//! - The proof-of-work is a SHA256 hash over the same bytes as the signature.
//!   The lower the calculated hash, the more work is thereby proved to have
//!   been performed in searching fpr the proof-of-work nonce.
//! - The specific hash used over these bytes is determined by the specific
//!   cryptographic signature algorithm being used.  For example, the initial
//!   `ed25519` system implemented specifies SHA2-512.
use crate::{
  crypto::{
    algos::{
      ed25519::{Ed25519PublicKey, Ed25519Signature},
      AuthenticationKey, CryptoKey, CryptoSignature,
    },
    CryptoErr, CryptoKeyTypes, CryptoSignatureTypes, GlyphHash, HashContext,
    Sha256Context, Sha256Hash, Sha3Hash,
  },
  util::debug::UnquotedDebugString,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, U16},
  FromGlyph, Glyph, GlyphDecodeErr, GlyphErr, GlyphHeader, GlyphOffset,
  GlyphType, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  slice::from_raw_parts,
};
use std::ops::Deref;

/// The default number of hashes to check when creating a new cryptographic
/// signature.
pub const DEFAULT_SIGN_POW: u32 = 10_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(packed)]
pub struct SignatureMetadata {
  what: GlyphHash,
  why:  GlyphHash,
  work: [u8; 16],
}

impl SignatureMetadata {
  pub fn new(
    what: GlyphHash,
    why: Option<GlyphHash>,
    work: Option<[u8; 16]>,
  ) -> Self {
    let work = work.unwrap_or_else(|| [0; 16]);
    let why = why.unwrap_or_else(|| GlyphHash::default());
    Self { what, why, work }
  }

  pub fn as_bytes(&self) -> &[u8] {
    // SAFETY: self is ZeroCopy and repr packed.
    unsafe {
      from_raw_parts(
        self as *const _ as *const u8,
        size_of::<SignatureMetadata>(),
      )
    }
  }

  pub fn has_reason(&self) -> bool {
    self.why != GlyphHash::default()
  }

  pub fn what_signed(&self) -> &GlyphHash {
    &self.what
  }

  pub fn why_signed(&self) -> &GlyphHash {
    &self.why
  }

  pub fn do_work(&mut self, hashes: u64) {
    self.do_work_fn(|bytes| {
      let mut ctx = Sha256Context::new();
      ctx.update(bytes);
      let work_iterations = hashes as u128;
      let mut first_hash = ctx.clone();
      first_hash.update(&(0u128.to_le_bytes())[..]);
      let mut low_hash = first_hash.finish();
      let mut low_i = 0;
      for i in 1..work_iterations {
        let mut work_hash = ctx.clone();
        work_hash.update(&(i.to_le_bytes())[..]);
        let work_hash = work_hash.finish();
        if work_hash < low_hash {
          low_i = i;
          low_hash = work_hash;
        }
      }
      low_i.to_le_bytes()
    });
  }

  pub fn do_work_fn<F: FnOnce(&[u8; 64]) -> [u8; 16]>(&mut self, f: F) {
    // SAFETY: Struct is packed, we want what/why as a simple byte slice
    // to the caller can calculate a SHA256 hash over it.
    let what_why_bytes =
      unsafe { core::mem::transmute::<&SignatureMetadata, &[u8; 64]>(&self) };
    let work = f(what_why_bytes);
    self.work = work;
  }

  pub fn show_work(&self) -> Sha256Hash {
    let mut hash_context = Sha256Context::new();
    hash_context.update(&self.what.as_ref());
    hash_context.update(&self.why.as_ref());
    hash_context.update(&self.work[..]);
    hash_context.finish()
  }
}

// SAFETY: All components are also zero-copy, repr is packed.
unsafe impl ZeroCopy for SignatureMetadata {}

/// The zero-copy header for signature glyphs
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
struct SignatureGlyphHeader {
  version:  u8,
  flags:    u8,
  /// An identifier for the cryptographic algorithm used.
  sig_type: U16,
  /// The length of the cryptographic signature, in bytes.
  sig_len:  U16,
  /// The length of the public key used to verify the signature, in bytes.
  key_len:  U16,
  metadata: SignatureMetadata,
}

impl SignatureGlyphHeader {
  /// The associated signature glyph contains a signing statement.
  const INCLUDES_REASON: u8 = 0b0000_0001;

  fn includes_reason(&self) -> bool {
    self.flags & Self::INCLUDES_REASON != 0
  }

  fn sig_type(&self) -> CryptoSignatureTypes {
    self.sig_type.get().into()
  }

  fn signature_len(&self) -> usize {
    self.sig_len.get() as usize
  }

  fn key_len(&self) -> usize {
    self.key_len.get() as usize
  }
}

/// SAFETY: All components are also zero-copy.
unsafe impl ZeroCopy for SignatureGlyphHeader {}

/// A cryptographically verifiable signature.
///
/*  Binary format
   - Glyph and SignatureGlyph headers, with glyph and signature metadata
   - Signature bytes (type and length specified in the header)
   - Key bytes (length specified in header, type implied from signature type)
   - Optional glyph for the signing statement (hash must match `why` in header)
*/
#[derive(Clone)]
pub struct SignatureGlyph<G> {
  glyph:            G,
  key_offset:       GlyphOffset,
  statement_offset: GlyphOffset,
}

impl<G: Deref<Target = Glyph>> SignatureGlyph<G> {
  fn header(&self) -> &SignatureGlyphHeader {
    // SAFETY: Header is zero-copy, was read and bounds checked at creation.
    unsafe { SignatureGlyphHeader::bbrf_u(self.glyph.content(), &mut 0) }
  }

  fn sig_bytes(&self) -> &[u8] {
    // SAFETY: Already bounds checked when glyph was read.
    unsafe {
      let mut cursor = size_of::<SignatureGlyphHeader>();
      u8::bbrfs_u(
        self.glyph.content(),
        &mut cursor,
        self.header().signature_len(),
      )
    }
  }

  fn key_bytes(&self) -> &[u8] {
    // SAFETY: Already bounds checked when glyph was read.
    unsafe {
      let mut cursor = self.key_offset.cursor(0);
      u8::bbrfs_u(self.glyph.content(), &mut cursor, self.header().key_len())
    }
  }

  pub fn signature_metadata(&self) -> &SignatureMetadata {
    &self.header().metadata
  }

  pub fn what_signed(&self) -> &GlyphHash {
    self.signature_metadata().what_signed()
  }

  pub fn why_signed_hash(&self) -> &GlyphHash {
    self.signature_metadata().why_signed()
  }

  pub fn why_signed_statement(&self) -> Option<&Glyph> {
    let mut cursor = self.statement_offset.cursor(0);
    if cursor > 0 {
      let glyph = Glyph::read(self.glyph.content(), &mut cursor).ok()?;
      // This will invisibly ignore a corrupt why signed statement.  Is this
      // the correct behavior?
      if &glyph.glyph_hash() == self.why_signed_hash() {
        Some(glyph)
      } else {
        None
      }
    } else {
      None
    }
  }

  /// If the signature is valid, return the fingerprint of the cryptographic key
  /// used to create the signature.
  pub fn valid_for(&self) -> Result<Sha3Hash, CryptoErr> {
    match self.header().sig_type() {
      CryptoSignatureTypes::Ed25519 => {
        let sig = Ed25519Signature::deserialize(
          CryptoSignatureTypes::Ed25519,
          self.sig_bytes(),
        )?;
        let key = Ed25519PublicKey::deserialize(
          CryptoKeyTypes::Ed25519Public,
          self.key_bytes(),
          &[],
        )?;
        if key
          .authenticate(self.signature_metadata().as_bytes(), &sig)
          .is_ok()
        {
          Ok(*key.fingerprint())
        } else {
          Err(CryptoErr::SignatureInvalid)
        }
      },
      CryptoSignatureTypes::Unknown => Err(CryptoErr::SignatureTypeUnknown(
        self.header().sig_type.get(),
      )),
    }
  }

  pub fn show_work(&self) -> Sha256Hash {
    self.signature_metadata().show_work()
  }
}

impl<G: Deref<Target = Glyph>> ToGlyph for SignatureGlyph<G> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    self.glyph.glyph_encode(target, cursor)
  }

  fn glyph_len(&self) -> usize {
    self.glyph.glyph_len()
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for SignatureGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphDecodeErr<G>> {
    let parse_result = || {
      glyph.header().confirm_type(GlyphType::Signature)?;
      let content = glyph.content();
      let cursor = &mut 0;

      let sgh = SignatureGlyphHeader::bbrf(content, cursor)?;
      let _sig_bytes = u8::bbrfs(content, cursor, sgh.signature_len())?;
      *cursor = round_to_word(*cursor);
      let key_offset = GlyphOffset::new(*cursor)?;
      let _key_bytes = u8::bbrfs(content, cursor, sgh.key_len())?;
      *cursor = round_to_word(*cursor);
      let statement_offset = if sgh.includes_reason()
        && sgh.metadata.why_signed() != &GlyphHash::default()
      {
        GlyphOffset::new(*cursor)?
      } else {
        GlyphOffset::new(0).unwrap()
      };

      Result::<_, GlyphErr>::Ok((key_offset, statement_offset))
    };

    match parse_result() {
      Ok((key_offset, statement_offset)) => Ok(Self {
        glyph,
        key_offset,
        statement_offset,
      }),
      Err(err) => Err(GlyphDecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for SignatureGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("CryptoSignature");
    df.field("proof_of_work", &self.signature_metadata().show_work());
    df.field("what_signed", self.what_signed());
    df.field("why_signed_hash", self.why_signed_hash());
    match self.valid_for() {
      Ok(fingerprint) => {
        df.field("valid_for", &fingerprint);
      },
      Err(_err) => {
        df.field("valid_for", &UnquotedDebugString("INVALID"));
        df.field("signature_type", &self.header().sig_type());
        df.field("signature_bytes", &self.sig_bytes());
      },
    }
    if let Some(statement) = self.why_signed_statement() {
      df.field("why_signed_statement", &statement.as_dyn());
    }
    df.finish()
  }
}

// #[derive(Clone, Debug)]
// enum SignatureInner {
//   Ed25519(Ed25519Signature, Ed25519PublicKey),
// }

// impl SignatureInner {
//   fn read(
//     crypto_type: SignatureType,
//     sig_bytes: &[u8],
//     key_bytes: &[u8],
//   ) -> Result<Self, GlyphErr> {
//     match crypto_type {
//       SignatureType::Ed25519 => {
//         let sig = Ed25519Signature::read(sig_bytes, &mut 0)?;
//         let key = Ed25519PublicKey::read(key_bytes, &[])?;
//         todo!()
//       },
//       SignatureType::Unknown => {
//         todo!()
//       },
//     }
//   }
//
//   fn write_sig(
//     &self,
//     target: &mut [u8],
//     cursor: &mut usize,
//   ) -> Result<(), GlyphErr> {
//     match self {
//       SignatureInner::Ed25519(sig, _) => sig.write(target, cursor),
//     }
//   }
//
//   fn write_key(
//     &self,
//     target: &mut [u8],
//     cursor: &mut usize,
//   ) -> Result<(), GlyphErr> {
//     match self {
//       SignatureInner::Ed25519(_, key) => key.write_public(target, cursor),
//     }
//   }
//
//   fn crypto_signature_type(&self) -> SignatureType {
//     match self {
//       SignatureInner::Ed25519(_, _) => SignatureType::Ed25519,
//     }
//   }
//
//   fn signature_len(&self) -> usize {
//     match self {
//       SignatureInner::Ed25519(sig, _) => ED25519_SIGNATURE_LEN,
//     }
//   }
//
//   fn key_len(&self) -> usize {
//     match self {
//       SignatureInner::Ed25519(_, _) => ED25519_KEY_LEN,
//     }
//   }
// }

// pub enum ProofOfWork<'a> {
//   None,
//   CpuLow,
//   CpuDefault,
//   CpuHigh,
//   Custom(&'a dyn Fn(&Sha256Context) -> [u8; 16]),
// }
//
// impl<'a> ProofOfWork<'a> {
//   pub fn calculate_sha2(&self, ctx: &Sha256Context) -> [u8; 16] {
//     match self {
//       ProofOfWork::None => [0; 16],
//       ProofOfWork::CpuLow => pow2(ctx, 1_000),
//       ProofOfWork::CpuDefault => pow2(ctx, 10_000),
//       ProofOfWork::CpuHigh => pow2(ctx, 100_000),
//       ProofOfWork::Custom(func) => func(ctx),
//     }
//   }
// }
//
// impl Default for ProofOfWork<'static> {
//   fn default() -> Self {
//     ProofOfWork::CpuDefault
//   }
// }
//
// pub trait ProofOfWorkGenerator {
//   fn pow_generate(
//     &self,
//     reason: &SigningReason,
//     what_signed: &GlyphHash,
//     reason_glyph: Option<&[u8]>,
//   ) -> [u8; 16];
// }
//
// fn pow2(ctx: &Sha256Context, iterations: u32) -> [u8; 16] {
//   let work_iterations = iterations as u128;
//   let mut first_hash = ctx.clone();
//   first_hash.update(&(0u128.to_le_bytes())[..]);
//   let mut low_hash = first_hash.finish();
//   let mut low_i = 0;
//   for i in 1..work_iterations {
//     let mut work_hash = ctx.clone();
//     work_hash.update(&(i.to_le_bytes())[..]);
//     let work_hash = work_hash.finish();
//     if work_hash < low_hash {
//       low_i = i;
//       low_hash = work_hash;
//     }
//   }
//   low_i.to_le_bytes()
// }

fn signature_glyph_len<SIG: CryptoSignature>(
  signature: &SIG,
  key: &SIG::AuthenticationKey,
  statement: Option<&Glyph>,
) -> usize {
  size_of::<GlyphHeader>()
    + size_of::<SignatureGlyphHeader>()
    + round_to_word(signature.signature_length())
    + round_to_word(key.public_len())
    + statement.map(|s| s.glyph_len()).unwrap_or(0)
}

fn signature_glyph_write<SIG: CryptoSignature>(
  signature: &SIG,
  key: &SIG::AuthenticationKey,
  metadata: SignatureMetadata,
  signing_statement: Option<&Glyph>,
  target: &mut [u8],
  cursor: &mut usize,
) -> Result<(), GlyphErr> {
  let glyph_length = signature_glyph_len(signature, key, signing_statement);
  GlyphHeader::new(GlyphType::Signature, glyph_length)?.bbwr(target, cursor)?;
  let mut flags = 0;
  if signing_statement.is_some() {
    flags |= SignatureGlyphHeader::INCLUDES_REASON;
  }
  SignatureGlyphHeader {
    version: 0,
    flags,
    sig_type: signature.signature_type().into(),
    sig_len: signature.signature_length().try_into()?,
    key_len: key.public_len().try_into()?,
    metadata,
  }
  .bbwr(target, cursor)?;
  u8::bbwrs(&signature.signature_bytes().as_ref(), target, cursor)?;
  pad_to_word(target, cursor)?;
  u8::bbwrs(key.public_bytes().as_ref(), target, cursor)?;
  pad_to_word(target, cursor)?;
  if let Some(statement) = signing_statement {
    statement.glyph_encode(target, cursor)?;
  }
  Ok(())
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//
//
// }
