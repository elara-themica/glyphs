//! Cryptographic signatures and related types.
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
      ed25519::{
        Ed25519PrivateKey, Ed25519PublicKey, Ed25519Signature, ED25519_KEY_LEN,
        ED25519_SIGNATURE_LEN,
      },
      CryptoKeyTypes,
    },
    CryptoErr, CryptoKeyGlyph, CryptoSignatureOldTrait, GlyphHash,
    GlyphsAuthenticationKey, GlyphsCryptographicKey, GlyphsSigningKey,
    HashContext, Sha256Context, Sha256Hash, Sha3Hash,
  },
  glyph_read,
  misc::DateTime,
  util::debug::UnquotedDebugString,
  zerocopy::{ZeroCopy, U16},
  EncodedGlyph, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ParsedGlyph, ToGlyph, UnsafeGlyph,
};
use core::fmt::{Debug, Formatter};
use rand::{CryptoRng, RngCore};

/// The default number of hashes to check when creating a new cryptographic
/// signature.
pub const DEFAULT_SIGN_POW: u32 = 10_000;

/// A key used for creating cryptographically verifiable signatures.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SigningKey {
  /// Data specific to the type of cryptographic key being used.
  key: SigningKeyInner,
}

/// Data specific to the type of cryptographic key being used.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SigningKeyInner {
  /// An Ed25519 private key.
  Ed25519(Ed25519PrivateKey),
}

impl SigningKey {
  /// Generates a new signing key using the default cryptographic algorithm
  /// (currently Ed25519, though this is not guaranteed in the future).
  ///
  /// # Parameters
  /// - `rng`: A mutable reference to a random number generator that implements
  ///   both `RngCore` and `CryptoRng`. This should be a high-quality source
  ///   of randomness to ensure the security of the generated key.
  /// - `expires`:  An optional time at which the key will expire.  If `None`,
  ///   the key will never expire.
  ///
  /// # Returns
  /// A `SigningKey` enum instance wrapping the generated Ed25519 private key.
  ///
  /// # Security Warning
  /// The security of the generated signing key heavily depends on the quality
  /// of the randomness provided by the `rng`. Ensure that you use a cryptographically
  /// secure RNG to avoid compromising the key's security properties.
  ///
  /// # Example
  /// ```
  /// use rand::rngs::OsRng;
  /// use glyphs::crypto::SigningKey;
  ///
  /// let mut rng = OsRng;
  /// let signing_key = SigningKey::new(&mut rng, None);
  /// ```
  pub fn new<R: RngCore + CryptoRng>(
    rng: &mut R,
    expires: Option<DateTime>,
  ) -> Self {
    Self::new_ed25519(rng, expires)
  }

  /// Generates a new signing key using the Ed25519 cryptographic algorithm
  ///
  /// # Parameters
  /// - `rng`: A mutable reference to a random number generator that implements
  ///   both `RngCore` and `CryptoRng`. This should be a high-quality source
  ///   of randomness to ensure the security of the generated key.
  /// - `expires`:  An optional time at which the key will expire.  If `None`,
  ///   the key will never expire.
  ///
  /// # Returns
  /// A `SigningKey` enum instance wrapping the generated Ed25519 private key.
  ///
  /// # Security Warning
  /// The security of the generated signing key heavily depends on the quality
  /// of the randomness provided by the `rng`. Ensure that you use a cryptographically
  /// secure RNG to avoid compromising the key's security properties.
  ///
  /// # Example
  /// ```
  /// use rand::rngs::OsRng;
  /// use glyphs::crypto::SigningKey;
  ///
  /// let mut rng = OsRng;
  /// let signing_key = SigningKey::new_ed25519(&mut rng, None);
  /// ```
  pub fn new_ed25519<R: RngCore + CryptoRng>(
    rng: &mut R,
    expires: Option<DateTime>,
  ) -> Self {
    let sk = Ed25519PrivateKey::generate(rng, expires);
    Self {
      key: SigningKeyInner::Ed25519(sk),
    }
  }

  // /// Generates a new cryptographic signature for the given data.
  // ///
  // /// # Parameters
  // /// - `what_signed`: The hash of the data being signed. This serves as the
  // ///   unique identifier of the content to be signed.
  // /// - `statement`: A description of the reason for signing. This can include
  // ///    metadata explaining the purpose of the signature, or additional
  // ///    context about the signing operation.
  // /// - `work_level`: All signatures include a proof of work, giving
  // ///   applications a defense against malicious actors bulk-signing data.  By
  // ///   default, the number of hashes checked by the CPU is set by
  // ///   `DEFAULT_SIGN_POW`, but that can be overridden here.  If an extensive
  // ///   proof of work is required, the `sign_full()` version of this function
  // ///   allows users to provide a customized proof of work.
  // ///
  // /// # Returns
  // /// - On success, returns a `CryptoSignature` object that contains the generated
  // ///   signature along with all relevant data.
  // /// - An error of type `SignatureError` if the signing process fails due to an
  // ///   internal issue or invalid data.
  // ///
  // /// # Example
  // /// ```
  // /// use rand::rngs::OsRng;
  // /// use glyphs::crypto::{SigningKey, GlyphHash, SigningReason, CryptographicHash};
  // ///
  // /// let mut rng = OsRng;
  // /// let signing_key = SigningKey::new(&mut rng, None);
  // /// let hash = GlyphHash::new(b"Thing to Sign");
  // /// let reason = SigningReason::Unspecified;
  // ///
  // /// match signing_key.sign(hash, reason, None) {
  // ///     Ok(signature) => println!("Generated signature: {:?}", signature),
  // ///     Err(error) => eprintln!("Error signing data: {:?}", error),
  // /// }
  // /// ```
  // pub fn sign(
  //   &self,
  //   what_signed: GlyphHash,
  //   statement: SigningReason,
  //   work_level: Option<u32>,
  // ) -> Result<SignatureGlyph<BoxGlyph>, CryptoErr> {
  //   let work_level = work_level.unwrap_or(DEFAULT_SIGN_POW);
  //   let signature =
  //     self.sign_full(what_signed, statement, |hash, statement| {
  //       proof_of_work_cpu(work_level, hash, statement)
  //     })?;
  //   Ok(signature)
  // }
  //
  // ///
  // pub fn sign_full<POW>(
  //   &self,
  //   what_signed: GlyphHash,
  //   reason: SigningReason,
  //   pow_gen: POW,
  // ) -> Result<SignatureGlyph<BoxGlyph>, CryptoErr>
  // where
  //   POW: for<'a> Fn(&'a GlyphHash, &'a SigningReason) -> [u8; 16],
  // {
  //   // Calculate proof of work.
  //   let work_proof = pow_gen(&what_signed, &reason);
  //   // Create the appropriate cryptographic signature
  //   let sig = match &self.key {
  //     SigningKeyInner::Ed25519(key) => {
  //       let mut hasher = key.new_hash_context();
  //       hasher.update(&reason.data()[..]);
  //       hasher.update(what_signed.as_ref());
  //       if let Some(glyph) = reason.glyph() {
  //         hasher.update(glyph.as_ref());
  //       }
  //       hasher.update(&work_proof[..]);
  //       let sig = key.sign_pre_hashed(hasher)?;
  //       SignatureInner::Ed25519(sig, key.public_key().clone())
  //     },
  //   };
  //
  //   // Instantiate a `CryptoSignature`.
  //   Ok(SignatureGlyph {
  //     reason,
  //     what_signed,
  //     work_proof,
  //     inner: sig,
  //   })
  // }
}

impl ToGlyph for SigningKey {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.glyph_encode(target, cursor),
    }
  }

  fn glyph_len(&self) -> usize {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.glyph_len(),
    }
  }
}

impl<'a, G: Glyph> TryFrom<&'a CryptoKeyGlyph<G>> for SigningKey {
  type Error = GlyphErr;

  fn try_from(value: &'a CryptoKeyGlyph<G>) -> Result<Self, Self::Error> {
    match value.key_type() {
      CryptoKeyTypes::Ed25519Private => {
        let sk = Ed25519PrivateKey::try_from(value)?;
        Ok(Self {
          key: SigningKeyInner::Ed25519(sk),
        })
      },
      _ => Err(GlyphErr::CryptoErr(CryptoErr::InvalidSigningKeyType(
        value.key_type(),
      ))),
    }
  }
}

impl<G: Glyph> FromGlyph<G> for SigningKey {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    let ckg = CryptoKeyGlyph::from_glyph(glyph)?;
    match SigningKey::try_from(&ckg) {
      Ok(sk) => Ok(sk),
      Err(err) => Err(FromGlyphErr::new(ckg.into_inner(), err)),
    }
  }
}

impl GlyphsCryptographicKey for SigningKey {
  fn key_type(&self) -> CryptoKeyTypes {
    match &self.key {
      SigningKeyInner::Ed25519(_) => CryptoKeyTypes::Ed25519Private,
    }
  }

  fn fingerprint(&self) -> Sha3Hash {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.fingerprint(),
    }
  }

  fn expires(&self) -> &DateTime {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.expires(),
    }
  }

  fn read(
    key_type: CryptoKeyTypes,
    expires: &DateTime,
    public: &[u8],
    private: &[u8],
  ) -> Result<Self, GlyphErr> {
    match key_type {
      CryptoKeyTypes::Ed25519Private => {
        let key = Ed25519PrivateKey::read(key_type, expires, public, private)?;
        Ok(Self {
          key: SigningKeyInner::Ed25519(key),
        })
      },
      _ => Err(GlyphErr::CryptoErr(CryptoErr::InvalidSigningKey)),
    }
  }

  fn key_len_public(&self) -> usize {
    ED25519_KEY_LEN
  }

  fn write_public(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.write_public(target, cursor),
    }
  }

  fn key_len_private(&self) -> usize {
    ED25519_KEY_LEN
  }

  fn write_private(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match &self.key {
      SigningKeyInner::Ed25519(sk) => sk.write_private(target, cursor),
    }
  }
}

impl Debug for SigningKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("SigningKey");
    match &self.key {
      SigningKeyInner::Ed25519(sk) => {
        df.field("key_type", &CryptoKeyTypes::Ed25519Private);
        df.field("fingerprint", &sk.fingerprint());
        df.field("expires", &sk.expires());
      },
    }
    df.finish()
  }
}

pub struct Signature<G: Glyph> {
  /// The reason the signature is being created
  reason:        SigningReason,
  /// The hash of the content being signed.
  what_signed:   GlyphHash,
  /// An optional signing statement, if the reason alone is insufficient.
  statement:     Option<G>,
  /// A proof-of-work nonce
  proof_of_work: [u8; 16],
  /// The cryptographic signature and public key.
  crypto:        SignatureInner,
}

impl<G: Glyph> ToGlyph for Signature<G> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let content_len = self.glyph_len().saturating_sub(size_of::<GlyphHeader>());
    GlyphHeader::new(GlyphType::Signature, content_len)?
      .bbwr(target, cursor)?;

    let mut flags: u8 = 0;
    if self.statement.is_some() {
      flags |= SignatureGlyphHeader::FLAG_HAS_STATEMENT;
    }
    SignatureGlyphHeader {
      version: 0,
      flags,
      sig_type: self.crypto.crypto_signature_type().into(),
      sig_len: self.crypto.signature_len().try_into()?,
      key_len: self.crypto.key_len().try_into()?,
      what_signed: self.what_signed.clone(),
      reason_id: U16::from(self.reason.reason_id()),
      reason_data: self.reason.data(),
    }
    .bbwr(target, cursor)?;
    if let Some(statement) = self.statement.as_ref() {
      statement.glyph_encode(target, cursor)?;
    }
    u8::bbwrs(self.proof_of_work.as_ref(), target, cursor)?;
    match &self.crypto {
      SignatureInner::Ed25519(sig, key) => {
        sig.write(target, cursor)?;
        key.write_public(target, cursor)?;
      },
    }
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<SignatureGlyphHeader>()
      + if let Some(statement) = self.statement.as_ref() {
        statement.glyph_len()
      } else {
        0
      }
      + self.proof_of_work.len()
      + match &self.crypto {
        SignatureInner::Ed25519(_, _) => {
          ED25519_SIGNATURE_LEN + ED25519_KEY_LEN
        },
      }
  }
}

impl<G: Glyph> FromGlyph<G> for Signature<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    todo!()
  }
}

/// An enumeration of reasons for providing a cryptographic signature.
#[derive(Copy, Clone)]
#[repr(u16)]
pub enum SigningReason {
  Unspecified = 0x0000,
  SeeStatement = 0x0001,
  UnknownReasonType(U16) = 0xFFFF,
}

impl SigningReason {
  fn reason_id(&self) -> u16 {
    match self {
      SigningReason::UnknownReasonType(type_id) => type_id.get(),
      // SAFETY: Because `Self` is marked `repr(u16)`, its layout is a `repr(C)` `union`
      // between `repr(C)` structs, each of which has the `u16` discriminant as its first
      // field, so we can read the discriminant without offsetting the pointer.
      _ => unsafe { *<*const _>::from(self).cast::<u16>() },
    }
  }

  /// Returns the bytes that will represent this reason in the signature header.
  ///
  // These bytes must match what is written into the target glyph, as the
  // signature will be calculated based on it.
  pub(super) fn data(&self) -> [u8; 14] {
    match self {
      // For reason types which store other data in these bytes...
      _ => [0; 14],
    }
  }

  #[allow(unused_variables)]
  pub fn read<'a>(
    reason_id: U16,
    reason_data: &[u8; 14],
  ) -> Result<SigningReason, GlyphErr> {
    match reason_id.get() {
      0x0000 => Ok(SigningReason::Unspecified),
      0x0001 => Ok(SigningReason::SeeStatement),
      _ => Ok(SigningReason::UnknownReasonType(reason_id)),
    }
  }
}

impl Debug for SigningReason {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match self {
      SigningReason::Unspecified => {
        write!(f, "SigningReason::Unspecified")
      },
      SigningReason::SeeStatement => {
        write!(f, "SigningReason::SeeStatement")
      },
      SigningReason::UnknownReasonType(tid) => {
        write!(f, "SigningReason::UnknownReasonType({:?})", tid)
      },
    }
  }
}

/// The zero-copy header for signature glyphs
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct SignatureGlyphHeader {
  version:     u8,
  flags:       u8,
  /// An identifier for the cryptographic algorithm used.
  sig_type:    U16,
  /// The length of the cryptographic signature, in bytes.
  sig_len:     U16,
  /// The length of the public key used to verify the signature, in bytes.
  key_len:     U16,
  /// An identifier for the reason the signature was being made.
  /// See [`SigningReason`].
  reason_id:   U16,
  /// Space for tagged union identified by `reason_id`.
  reason_data: [u8; 14],
  /// The content hash of what is being signed.
  what_signed: GlyphHash,
}

/// SAFETY: All components are also zero-copy.
unsafe impl ZeroCopy for SignatureGlyphHeader {}

impl SignatureGlyphHeader {
  /// The associated signature glyph contains a signing statement.
  const FLAG_HAS_STATEMENT: u8 = 0b0000_0001;

  fn has_comment(&self) -> bool {
    self.flags & Self::FLAG_HAS_STATEMENT != 0
  }

  fn sig_len(&self) -> usize {
    self.sig_len.get() as usize
  }

  fn pk_len(&self) -> usize {
    self.key_len.get() as usize
  }

  fn what_signed(&self) -> &GlyphHash {
    &self.what_signed
  }

  fn sig_type(&self) -> SignatureType {
    self.sig_type.get().into()
  }

  fn reason(&self) -> SigningReason {
    todo!()
  }
}

/// A cryptographically verifiable signature.
///
/*  Binary format
   - Glyph header and SignatureGlyphHeader
     - Includes metadata, reason id and data, hash of signed content
   - Optional signing statement glyph
   - [u8; 16] nonce as a proof of work
   - Cryptographic signature (length specified in header, 8-byte padded)
   - Corresponding public key (length specified in header).
*/
#[derive(Clone)]
pub struct SignatureGlyph<G> {
  glyph:         G,
  header:        *const SignatureGlyphHeader,
  statement:     Option<UnsafeGlyph>,
  proof_of_work: *const [u8; 16],
  sig_bytes:     *const u8,
  key_bytes:     *const u8,
  inner:         Result<SignatureInner, GlyphErr>,
}

impl<G: Glyph> SignatureGlyph<G> {
  fn header(&self) -> &SignatureGlyphHeader {
    unsafe { &*self.header }
  }

  fn signed_bytes(&self) -> &[u8] {
    todo!()
  }

  pub fn what_signed(&self) -> &GlyphHash {
    self.header().what_signed()
  }

  pub fn reason(&self) -> SigningReason {
    self.header().reason()
  }

  /// If the signature is valid, return the fingerprint of the cryptographic key
  /// used to create the signature.
  pub fn valid_for(&self) -> Result<Sha3Hash, CryptoErr> {
    // match &self.inner {
    //   SignatureInner::Ed25519(sig, pk) => {
    //     let mut hasher = pk.new_hash_context();
    //     ed25519_dalek::Digest::update(&mut hasher, &self.reason.data()[..]);
    //     ed25519_dalek::Digest::update(&mut hasher, &self.what_signed.as_ref());
    //     if let Some(glyph) = self.reason.glyph() {
    //       ed25519_dalek::Digest::update(&mut hasher, glyph.as_ref());
    //     }
    //     ed25519_dalek::Digest::update(&mut hasher, &self.work_proof);
    //     if let Ok(()) = pk.verify_pre_hashed(hasher, sig) {
    //       Ok(pk.fingerprint())
    //     } else {
    //       Err(CryptoErr::SignatureInvalid)
    //     }
    //   },
    //   SignatureInner::Unknown { type_id } => {
    //     Err(CryptoErr::SignatureTypeUnknown(*type_id))
    //   },
    // }

    todo!()
  }

  pub fn proof_of_work(&self) -> Sha256Hash {
    // let mut hash_context = Sha256Context::new();
    // hash_context.update(&self.reason.data()[..]);
    // hash_context.update(self.what_signed.as_ref());
    // if let Some(glyph) = self.reason.glyph() {
    //   hash_context.update(glyph.as_ref());
    // }
    // hash_context.update(&self.work_proof[..]);
    // hash_context.finish()

    todo!()
  }
}

impl<G: Glyph> ToGlyph for SignatureGlyph<G> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    todo!()
  }

  fn glyph_len(&self) -> usize {
    todo!()
  }
}

impl<G: Glyph> FromGlyph<G> for SignatureGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = glyph.confirm_type(GlyphType::Signature) {
      return Err(FromGlyphErr::new(glyph, err));
    }
    let content = glyph.content();
    let cursor = &mut 0;

    let sgh = match SignatureGlyphHeader::bbrf(content, cursor) {
      Ok(sgh) => sgh,
      Err(err) => return Err(FromGlyphErr::new(glyph, err)),
    };
    /* We need to read the following, not present in the header.
      - Optional signing statement glyph
      - Proof of work
      - Sig bytes
      - Key bytes
    */
    let statement = if sgh.has_comment() {
      let pg = match glyph_read(content, cursor) {
        Ok(pg) => pg,
        Err(err) => return Err(FromGlyphErr::new(glyph, err)),
      };
      Some(UnsafeGlyph::from_parsed(pg))
    } else {
      None
    };
    let proof_of_work: &[u8; 16] = match u8::bbrfa(content, cursor) {
      Ok(pow) => pow,
      Err(err) => return Err(FromGlyphErr::new(glyph, err)),
    };
    let sig_bytes = match u8::bbrfs(content, cursor, sgh.sig_len()) {
      Ok(sig_bytes) => sig_bytes,
      Err(err) => return Err(FromGlyphErr::new(glyph, err)),
    };
    let key_bytes = match u8::bbrfs(content, cursor, sgh.pk_len()) {
      Ok(key_bytes) => key_bytes,
      Err(err) => return Err(FromGlyphErr::new(glyph, err)),
    };

    let inner = SignatureInner::read(sgh.sig_type(), sig_bytes, key_bytes);

    let header = sgh as *const _;
    let proof_of_work = proof_of_work as *const _;
    let sig_bytes = sig_bytes.as_ptr();
    let key_bytes = key_bytes.as_ptr();
    Ok(Self {
      glyph,
      header,
      statement,
      proof_of_work,
      sig_bytes,
      key_bytes,
      inner,
    })
  }
}

impl<G: Glyph> Debug for SignatureGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("CryptoSignature");
    df.field("what_signed", &self.what_signed());
    df.field("proof_of_work", &self.proof_of_work());
    match self.valid_for() {
      Ok(fingerprint) => {
        df.field("valid_for", &fingerprint);
      },
      Err(_err) => {
        df.field("valid_for", &UnquotedDebugString("INVALID"));
        df.field("signature", &self.inner);
      },
    }
    df.field("reason", &self.reason());
    df.finish()
  }
}

#[derive(Clone, Debug)]
enum SignatureInner {
  Ed25519(Ed25519Signature, Ed25519PublicKey),
}

impl SignatureInner {
  fn read(
    crypto_type: SignatureType,
    sig_bytes: &[u8],
    key_bytes: &[u8],
  ) -> Result<Self, GlyphErr> {
    match crypto_type {
      SignatureType::Ed25519 => {},
      SignatureType::Unknown => {
        todo!()
      },
    }
  }

  fn crypto_signature_type(&self) -> SignatureType {
    match self {
      SignatureInner::Ed25519(_, _) => SignatureType::Ed25519,
    }
  }

  fn signature_len(&self) -> usize {
    match self {
      SignatureInner::Ed25519(sig, _) => ED25519_SIGNATURE_LEN,
    }
  }

  fn key_len(&self) -> usize {
    match self {
      SignatureInner::Ed25519(_, _) => ED25519_KEY_LEN,
    }
  }
}

/// Identifies the type of cryptographic signature used.
// SAFETY: (1) All values must be contiguous, and (2) `Unknown` must be highest.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum SignatureType {
  Ed25519 = 0x0000,
  Unknown = 0x0001,
}

impl SignatureType {
  /// Returns the number of bytes needed to store the associated public key.
  pub fn pk_len(&self) -> usize {
    match self {
      SignatureType::Ed25519 => 32,
      SignatureType::Unknown => 0,
    }
  }

  /// Returns the number of bytes needed to store the cryptographic signature.
  pub fn sig_len(&self) -> usize {
    match self {
      SignatureType::Ed25519 => 64,
      SignatureType::Unknown => 0,
    }
  }
}

impl From<u16> for SignatureType {
  fn from(value: u16) -> Self {
    if value > SignatureType::Unknown as u16 {
      SignatureType::Unknown
    } else {
      unsafe { core::mem::transmute::<u16, SignatureType>(value) }
    }
  }
}

impl From<U16> for SignatureType {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<SignatureType> for u16 {
  fn from(value: SignatureType) -> Self {
    value as u16
  }
}

impl From<SignatureType> for U16 {
  fn from(value: SignatureType) -> Self {
    (value as u16).into()
  }
}

pub enum ProofOfWork<'a> {
  CpuLow,
  CpuDefault,
  CpuHigh,
  Custom(&'a dyn ProofOfWorkGenerator),
}

impl Default for ProofOfWork<'static> {
  fn default() -> Self {
    ProofOfWork::CpuDefault
  }
}

pub trait ProofOfWorkGenerator {
  fn pow_generate(
    &self,
    what_signed: &GlyphHash,
    reason_bytes: &[u8; 16],
    reason_glyph: Option<ParsedGlyph>,
  ) -> [u8; 16];
}

/// A simple proof-of-work calculation using the CPU
fn proof_of_work_cpu(
  iterations: u32,
  hash: &GlyphHash,
  reason: &SigningReason,
  statement: Option<&[u8]>,
) -> [u8; 16] {
  let mut base_work_hash = Sha256Context::new();
  base_work_hash.update(&reason.data()[..]);
  base_work_hash.update(hash.as_ref());
  if let Some(statement) = statement {
    base_work_hash.update(statement);
  }

  let work_iterations = iterations as u128;
  let mut first_hash = base_work_hash.clone();
  first_hash.update(&(0u128.to_le_bytes())[..]);
  let mut low_hash = first_hash.finish();
  let mut low_i = 0;
  for i in 1..work_iterations {
    let mut work_hash = base_work_hash.clone();
    work_hash.update(&(i.to_le_bytes())[..]);
    let work_hash = work_hash.finish();
    if work_hash < low_hash {
      low_i = i;
      low_hash = work_hash;
    }
  }
  low_i.to_le_bytes()
}
