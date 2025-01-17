//! Code related to cryptographic signatures generally.
//!
//! - Cryptographic signatures are generated in the [`Signature`] type, which
//!   also contains (1) a [`GlyphHash`] of what's being signed, (2) an optional
//!   "signing statement" glyph, to provide context to the signature, and (3) a
//!   [`CryptoSignature`] containing the actual cryptographic signature and the
//!    full public key.  This type can be converted to/from a [`SignatureGlyph`].
//! - Currently, only `ed25519` keys and signatures are supported.
//! - If you want to create a signed glyph, use [`SignedGlyphWriter`].  It will
//!   create a [`SignedGlyph`] that contains both the content and the signature.
//!
//! A [`SignatureGlyph`] has the following binary format:
//!
//! - An 8-byte header (see the private `SignatureGlyphHeader`)
//! - A 32-byte [`GlyphHash`] of what's being signed.
//! - An optional glyph providing context to the signature.
//! - A cryptographic signature, the format of which depends on the type of key
//!   scheme, which is specified in the header.  Currently, this only supports
//!   Ed25519 signatures.
//!   - Ed25519 signatures are written as a 32-byte public key and a 64-byte
//!     signature, per RFC 8032 (and the `ed25519-dalek` crate).
use crate::{
  crypto::{
    CryptographicHash, FingerprintKey, GlyphHash, KeyFingerprint, SigningKey,
  },
  glyph_close, glyph_read,
  zerocopy::{round_to_word, ZeroCopy, U16, U32},
  FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader, GlyphType,
  ParsedGlyph, ToGlyph,
};
use core::{mem::size_of, ops::Deref};

/// The expected length of a signature glyph with the given parameters,
/// in bytes.
pub fn signature_glyph_len(
  sig_type: CryptoSignatureTypes,
  signing_statement_len: Option<usize>,
) -> usize {
  size_of::<GlyphHeader>()
    + size_of::<SignatureGlyphHeader>()
    + size_of::<GlyphHash>()
    + signing_statement_len.unwrap_or_default()
    + match sig_type {
      CryptoSignatureTypes::Unknown => 0,
      CryptoSignatureTypes::Ed25519 => {
        ::ed25519_dalek::PUBLIC_KEY_LENGTH + ::ed25519_dalek::SIGNATURE_LENGTH
      },
    }
}

/// Public key and signature data for cryptographic signatures.
///
/// Because `CryptoSignature`s contain both the public key and the signature,
/// it can be used to verify
pub enum CryptoSignature {
  Invalid,
  Ed25519(::ed25519_dalek::VerifyingKey, ::ed25519_dalek::Signature),
}

impl CryptoSignature {
  pub fn new_ed25519(
    pk: ::ed25519_dalek::VerifyingKey,
    sig: ::ed25519_dalek::Signature,
  ) -> Self {
    Self::Ed25519(pk, sig)
  }

  pub fn valid_for(&self, message: &[u8]) -> Option<KeyFingerprint> {
    match self {
      CryptoSignature::Invalid => None,
      CryptoSignature::Ed25519(key, sig) => {
        if ::ed25519_dalek::Verifier::verify(key, message, sig).is_ok() {
          Some(key.key_fingerprint())
        } else {
          None
        }
      },
    }
  }

  /// The number of bytes necessary to write the cryptographic signature of
  /// the specified type.
  fn sig_len(type_id: CryptoSignatureTypes) -> usize {
    match type_id {
      CryptoSignatureTypes::Ed25519 => {
        ::ed25519_dalek::PUBLIC_KEY_LENGTH + ::ed25519_dalek::SIGNATURE_LENGTH
      },
      _ => 0,
    }
  }

  fn type_id(&self) -> CryptoSignatureTypes {
    match self {
      Self::Ed25519(_, _) => CryptoSignatureTypes::Ed25519,
      _ => CryptoSignatureTypes::Unknown,
    }
  }
}

impl FingerprintKey for CryptoSignature {
  fn key_fingerprint(&self) -> KeyFingerprint {
    match self {
      CryptoSignature::Invalid => KeyFingerprint::default(),
      CryptoSignature::Ed25519(pk, _) => pk.key_fingerprint(),
    }
  }
}

// SAFETY WARNING: If making changes here, update the related `impl From<U16>`
#[repr(u16)]
pub enum CryptoSignatureTypes {
  Ed25519 = 0x0000,
  Unknown = 0x0001,
}

impl From<u16> for CryptoSignatureTypes {
  fn from(src: u16) -> Self {
    if src > CryptoSignatureTypes::Unknown as u16 {
      CryptoSignatureTypes::Unknown
    } else {
      // SAFETY: Checked value
      unsafe { core::mem::transmute::<u16, CryptoSignatureTypes>(src) }
    }
  }
}

impl From<U16> for CryptoSignatureTypes {
  fn from(src: U16) -> Self {
    src.get().into()
  }
}

impl From<CryptoSignatureTypes> for u16 {
  fn from(src: CryptoSignatureTypes) -> Self {
    src as u16
  }
}

impl From<CryptoSignatureTypes> for U16 {
  fn from(src: CryptoSignatureTypes) -> Self {
    U16::from(src as u16)
  }
}

/// Creates a [`SignatureGlyph`]
pub struct Signer<S, K>
where
  S: Deref,
  S::Target: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  hash:      GlyphHash,
  statement: Option<S>,
  key:       K,
}

impl<S, K> Signer<S, K>
where
  S: Deref,
  S::Target: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new_with_statement(hash: GlyphHash, statement: S, key: K) -> Self {
    Self {
      hash,
      statement: Some(statement),
      key,
    }
  }
}

impl<K> Signer<&(), K>
where
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new(hash: GlyphHash, key: K) -> Self {
    Self {
      hash,
      statement: None,
      key,
    }
  }
}

impl<S, K> ToGlyph for Signer<S, K>
where
  S: Deref,
  S::Target: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    SignatureGlyphHeader::new(
      self.statement.is_some(),
      self.key.crypto_sig_type(),
    )
    .bbwr(target, cursor)?;
    let to_sign_start = *cursor;
    self.hash.bbwr(target, cursor)?;
    if let Some(statement) = &self.statement {
      statement.glyph_encode(target, cursor)?;
    }
    let to_sign = &target[to_sign_start..*cursor];
    let cs = self.key.deref().sign(to_sign)?;
    match cs {
      CryptoSignature::Ed25519(key, sig) => {
        u8::bbwrs(&key.as_bytes()[..], target, cursor)?;
        u8::bbwrs(&sig.to_bytes()[..], target, cursor)?;
      },
      _ => return Err(err!(debug, GlyphErr::WrongCryptoScheme)),
    }
    glyph_close(GlyphType::Signature, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    signature_glyph_len(
      self.key.crypto_sig_type(),
      match &self.statement {
        None => None,
        Some(statement) => Some(statement.glyph_len()),
      },
    )
  }
}

/// A header used in the encoding of signature glyphs.
#[repr(packed)]
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
struct SignatureGlyphHeader {
  version:    u8,
  flags:      u8,
  sig_type:   U16,
  reserved_2: U32,
}

/// SAFETY: All components are zero copy
unsafe impl ZeroCopy for SignatureGlyphHeader {}

impl SignatureGlyphHeader {
  const HAS_SIGNING_STATEMENT: u8 = 0b0000_0001;

  fn new(has_ss: bool, sig_type: CryptoSignatureTypes) -> Self {
    let mut flags: u8 = 0;
    if has_ss {
      flags |= Self::HAS_SIGNING_STATEMENT;
    }

    Self {
      version: 0,
      flags,
      sig_type: sig_type.into(),
      reserved_2: Default::default(),
    }
  }

  fn has_statement(&self) -> bool {
    self.flags & Self::HAS_SIGNING_STATEMENT != 0
  }

  fn sig_type(&self) -> CryptoSignatureTypes {
    CryptoSignatureTypes::from(self.sig_type)
  }
}

pub struct SignedGlyphWriter<M, S, K>
where
  M: ToGlyph,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  message:   M,
  statement: Option<S>,
  key:       K,
}

impl<M, K> SignedGlyphWriter<M, (), K>
where
  M: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new(message: M, key: K) -> Self {
    Self {
      message,
      statement: None,
      key,
    }
  }
}

impl<M, S, K> SignedGlyphWriter<M, S, K>
where
  M: ToGlyph,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new_with_statement(message: M, statement: S, key: K) -> Self {
    Self {
      message,
      statement: Some(statement),
      key,
    }
  }
}

impl<M, S, K> ToGlyph for SignedGlyphWriter<M, S, K>
where
  M: ToGlyph,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();

    // Write the message
    let msg_start = *cursor;
    self.message.glyph_encode(target, cursor)?;
    let msg_hash = GlyphHash::new(&target[msg_start..*cursor]);
    if let Some(statement) = &self.statement {
      Signer::new_with_statement(msg_hash, statement, &*self.key)
        .glyph_encode(target, cursor)?;
    } else {
      Signer::new(msg_hash, &*self.key).glyph_encode(target, cursor)?;
    }
    glyph_close(GlyphType::SignedGlyph, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + self.message.glyph_len()
      + signature_glyph_len(
        self.key.crypto_sig_type(),
        match &self.statement {
          None => None,
          Some(g) => Some(g.glyph_len()),
        },
      )
  }
}
pub struct SignedExtentWriter<E, S, K>
where
  E: AsRef<[u8]>,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  bytes:     E,
  statement: Option<S>,
  key:       K,
}

impl<E, K> SignedExtentWriter<E, (), K>
where
  E: AsRef<[u8]>,
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new(bytes: E, key: K) -> Self {
    Self {
      bytes,
      statement: None,
      key,
    }
  }
}

impl<E, S, K> SignedExtentWriter<E, S, K>
where
  E: AsRef<[u8]>,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  pub fn new_with_statement(bytes: E, statement: S, key: K) -> Self {
    Self {
      bytes,
      statement: Some(statement),
      key,
    }
  }
}

impl<E, S, K> ToGlyph for SignedExtentWriter<E, S, K>
where
  E: AsRef<[u8]>,
  S: ToGlyph,
  K: Deref,
  K::Target: SigningKey,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();

    // Since the signature will have a known length, and the rest of the
    // extent does not (without a header), we'll save room for the signature
    // first, and the rest of the bytes will be the extent.
    let mut sig_cursor = *cursor;
    let sig_len = signature_glyph_len(
      self.key.deref().crypto_sig_type(),
      self.statement.as_ref().map(|g| g.glyph_len()),
    );
    *cursor += sig_len;
    let extent_start = *cursor;

    // Write the extent we're going to sign
    u8::bbwrs(self.bytes.as_ref(), target, cursor)?;
    let extent_hash = GlyphHash::new(&target[extent_start..*cursor]);

    // Write the signature
    match &self.statement {
      None => {
        Signer::new(extent_hash, &*self.key)
          .glyph_encode(target, &mut sig_cursor)?;
      },
      Some(statement) => {
        Signer::new_with_statement(extent_hash, statement, &*self.key)
          .glyph_encode(target, &mut sig_cursor)?;
      },
    }
    debug_assert_eq!(sig_cursor, extent_start);
    glyph_close(GlyphType::SignedExtent, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + round_to_word(self.bytes.as_ref().len())
      + signature_glyph_len(
        self.key.crypto_sig_type(),
        match &self.statement {
          None => None,
          Some(g) => Some(g.glyph_len()),
        },
      )
  }
}

pub struct SignatureGlyph<B>
where
  B: Glyph,
{
  glyph:       B,
  signed_hash: *const GlyphHash,
  // SAFETY: This is a self reference to pinned bytes from glyph.content(). It
  // must not escape `SignatureGlyph` without being bound to the lifetime of
  // &self.  Access it through Self::statement().
  statement:   Option<ParsedGlyph<'static>>,
  cs:          CryptoSignature,
  valid_for:   Option<KeyFingerprint>,
}

impl<B> SignatureGlyph<B>
where
  B: Glyph,
{
  pub fn signed_hash(&self) -> &GlyphHash {
    // SAFETY:  Glyph content is always pinned.
    unsafe { &*self.signed_hash }
  }

  pub fn statement(&self) -> Option<ParsedGlyph<'_>> {
    // SAFETY: See note in struct.
    self.statement.clone()
  }

  pub fn valid_for(&self) -> Option<&KeyFingerprint> {
    self.valid_for.as_ref()
  }

  pub fn crypto_sig(&self) -> &CryptoSignature {
    &self.cs
  }
}

impl<B> FromGlyph<B> for SignatureGlyph<B>
where
  B: Glyph,
{
  fn from_glyph(glyph: B) -> Result<Self, FromGlyphErr<B>> {
    if let Err(err) = glyph.confirm_type(GlyphType::Signature) {
      return Err(err.into_fge(glyph));
    }

    let source = glyph.content_padded();
    let cursor = &mut 0;
    let header = match SignatureGlyphHeader::bbrf(source, cursor) {
      Ok(header) => header,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    let signed_start = *cursor;
    let signed_hash = match GlyphHash::bbrf(source, cursor) {
      Ok(hash) => hash,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    let signed_hash = signed_hash as *const GlyphHash;

    let statement = if header.has_statement() {
      let glyph = unsafe {
        let glyph = match glyph_read(source, cursor) {
          Ok(g) => g,
          Err(err) => return Err(err.into_fge(glyph)),
        };
        glyph.detach()
      };
      Some(glyph)
    } else {
      None
    };
    let signed = &source[signed_start..*cursor];
    let (cs, valid_for) = match header.sig_type() {
      CryptoSignatureTypes::Unknown => {
        return Err(err!(debug, GlyphErr::WrongCryptoScheme).into_fge(glyph))
      },
      CryptoSignatureTypes::Ed25519 => {
        let pk_bytes: &[u8; ::ed25519_dalek::PUBLIC_KEY_LENGTH] =
          match u8::bbrfa(source, cursor) {
            Ok(pk) => pk,
            Err(err) => return Err(err.into_fge(glyph)),
          };
        let sig_bytes: &[u8; ::ed25519_dalek::SIGNATURE_LENGTH] =
          match u8::bbrfa(source, cursor) {
            Ok(sig) => sig,
            Err(err) => return Err(err.into_fge(glyph)),
          };
        let pk = match ::ed25519_dalek::VerifyingKey::from_bytes(pk_bytes)
          .map_err(|_err| GlyphErr::Ed25519VerificationKeyInvalid)
        {
          Ok(pk) => pk,
          Err(err) => return Err(err.into_fge(glyph)),
        };
        let sig = ::ed25519_dalek::Signature::from_bytes(sig_bytes);
        let cs = CryptoSignature::new_ed25519(pk, sig);
        let valid_for = cs.valid_for(signed);
        (cs, valid_for)
      },
    };

    Ok(Self {
      glyph,
      signed_hash,
      statement,
      cs,
      valid_for,
    })
  }
}

pub struct SignedExtent<G>
where
  G: Glyph,
{
  glyph:         G,
  signed_extent: *const [u8],
  signature:     SignatureGlyph<ParsedGlyph<'static>>,
  valid:         bool,
}

impl<B> SignedExtent<B>
where
  B: Glyph,
{
  /// The signed extent
  pub fn signed_extent(&self) -> &[u8] {
    unsafe { &*self.signed_extent }
  }

  /// The signature
  pub fn signature(&self) -> &SignatureGlyph<ParsedGlyph> {
    &self.signature
  }

  /// The public key fingerprint that the signature was valid for, if any.
  pub fn valid_for(&self) -> Option<&KeyFingerprint> {
    self.signature.valid_for()
  }
}

impl<B> FromGlyph<B> for SignedExtent<B>
where
  B: Glyph,
{
  fn from_glyph(glyph: B) -> Result<Self, FromGlyphErr<B>> {
    if let Err(err) = glyph.confirm_type(GlyphType::SignedExtent) {
      return Err(err.into_fge(glyph));
    }
    let source = glyph.content();

    let cursor = &mut 0;
    let signature = unsafe {
      let glyph = match glyph_read(source, cursor) {
        Ok(g) => g,
        Err(err) => return Err(err.into_fge(glyph)),
      };
      glyph.detach()
    };
    let signature = match SignatureGlyph::from_glyph(signature) {
      Ok(signature) => signature,
      Err(err) => {
        let (_sig_glyph, err) = err.into_parts();
        return Err(err.into_fge(glyph));
      },
    };
    let extent = &source[*cursor..];
    let signed_hash_computed = GlyphHash::new(extent);
    let signed_hash_stored = signature.signed_hash();
    let valid = {
      if signed_hash_computed.eq(signed_hash_stored) {
        signature.valid_for().is_some()
      } else {
        false
      }
    };
    let signed_extent = extent as *const [u8];

    Ok(Self {
      glyph,
      signed_extent,
      signature,
      valid,
    })
  }
}

pub struct SignedGlyph<B>
where
  B: Glyph,
{
  glyph:     B,
  signed:    ParsedGlyph<'static>,
  signature: SignatureGlyph<ParsedGlyph<'static>>,
  valid:     bool,
}

impl<B> SignedGlyph<B>
where
  B: Glyph,
{
  /// The glyph that was signed
  pub fn signed_glyph(&self) -> ParsedGlyph<'_> {
    self.signed.clone()
  }

  /// The signature
  pub fn signature(&self) -> &SignatureGlyph<ParsedGlyph> {
    &self.signature
  }

  /// The public key fingerprint that the signature was valid for, if any.
  pub fn valid_for(&self) -> Option<&KeyFingerprint> {
    self.signature.valid_for()
  }
}

impl<B> FromGlyph<B> for SignedGlyph<B>
where
  B: Glyph,
{
  fn from_glyph(glyph: B) -> Result<Self, FromGlyphErr<B>> {
    if let Err(err) = glyph.confirm_type(GlyphType::SignedGlyph) {
      return Err(err.into_fge(glyph));
    }
    let source = glyph.content_padded();
    let cursor = &mut 0;
    let signed = unsafe {
      let glyph = match glyph_read(source, cursor) {
        Ok(g) => g,
        Err(err) => return Err(err.into_fge(glyph)),
      };
      glyph.detach()
    };
    let signature = unsafe {
      let sig_glyph = match glyph_read(source, cursor) {
        Ok(g) => g,
        Err(err) => return Err(err.into_fge(glyph)),
      };
      sig_glyph.detach()
    };
    let signature = match SignatureGlyph::from_glyph(signature) {
      Ok(sig_glyph) => sig_glyph,
      Err(err) => {
        let (_sig_glyph, err) = err.into_parts();
        return Err(err.into_fge(glyph));
      },
    };
    let signed_hash_computed = GlyphHash::new(signed.as_ref());
    let signed_hash_stored = signature.signed_hash();
    let valid = {
      if signed_hash_computed.eq(signed_hash_stored) {
        signature.valid_for().is_some()
      } else {
        false
      }
    };

    Ok(Self {
      glyph,
      signed,
      signature,
      valid,
    })
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    crypto::{ed25519_keypair_generate, TEST_PLAINTEXT},
    glyph_new,
  };
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;

  #[test]
  fn signatures() -> Result<(), GlyphErr> {
    //=== Raw Signatures ===//
    let statement_str = "NOT";

    let mut rng = ChaCha20Rng::from_seed([32; 32]);
    let (sk, pk) = ed25519_keypair_generate(&mut rng);

    let hash = GlyphHash::default();
    let signer = Signer::new(hash, &sk);
    let glyph = glyph_new(signer)?;

    let sig_glyph = SignatureGlyph::from_glyph(glyph.borrow())?;
    assert!(sig_glyph.statement().is_none());
    assert_eq!(sig_glyph.valid_for().unwrap(), &pk.key_fingerprint());

    let signer = Signer::new_with_statement(hash, "NOT", &sk);
    let glyph = glyph_new(signer)?;

    let sig_glyph = SignatureGlyph::from_glyph(glyph.borrow())?;
    let statement = sig_glyph.statement().unwrap();
    let s = <&str>::from_glyph(statement)?;

    assert_eq!(s, statement_str);
    assert_eq!(sig_glyph.valid_for().unwrap(), &pk.key_fingerprint());

    //=== Signed Glyphs ===//
    let signed_str = core::str::from_utf8(TEST_PLAINTEXT).unwrap();
    let sgw = SignedGlyphWriter::new(signed_str, &sk);
    let glyph = glyph_new(sgw)?;
    let sg = SignedGlyph::from_glyph(glyph)?;
    let signed = sg.signed_glyph();
    let s = <&str>::from_glyph(signed)?;
    assert_eq!(s, signed_str);
    assert_eq!(sg.valid_for().unwrap(), &pk.key_fingerprint());

    //=== Signed Extents ===//
    let sgw = SignedExtentWriter::new(TEST_PLAINTEXT, &sk);
    let glyph = glyph_new(sgw)?;
    let sg = SignedExtent::from_glyph(glyph)?;
    let signed = sg.signed_extent();
    assert_eq!(signed, TEST_PLAINTEXT);
    assert_eq!(sg.valid_for().unwrap(), &pk.key_fingerprint());

    Ok(())
  }
}
