//! Encryption and Signatures
//!
//!

pub(self) mod algos;

pub use algos::aes::*;

mod authenticate;
pub use authenticate::*;

mod sign;
pub use sign::*;

mod ciphertext;
pub use self::ciphertext::*;

mod hash;
pub use self::hash::*;

#[cfg(feature = "md5")]
pub use crate::crypto::hash::md5::*;

#[cfg(feature = "sha1")]
pub use crate::crypto::hash::sha1::*;

#[cfg(feature = "sha2")]
pub use crate::crypto::hash::sha256::*;

#[cfg(feature = "sha3")]
pub use crate::crypto::hash::sha3::*;

#[cfg(feature = "blake3")]
pub use crate::crypto::hash::blake3::*;

mod key_codec;
pub use self::key_codec::*;

mod password;
pub use self::password::*;

// mod sign_old;
// pub use self::sign_old::*;

use crate::{
  crypto::algos::CryptoKeyTypes, misc::DateTime, util::debug::ShortHexDump,
  GlyphErr,
};
use core::fmt::{Debug, Formatter};
use rand::{CryptoRng, Rng};

/// A number used once (for cryptography).
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Nonce<const N: usize>([u8; N]);

impl<const N: usize> Nonce<N> {
  /// Constructs a new `Nonce` with the provided data.
  ///
  /// # Warning
  ///
  /// You **must** ensure that the `data` provided to this constructor is
  /// either:
  ///
  /// 1. **Truly random** - The data must be generated using a high-quality
  ///    random number generator, ensuring that there's no possibility of
  ///    repetition.
  /// 2. **Generated in a cryptographically secure context** - For example, it
  ///    is derived from an ephemeral key in a context where the key and nonce
  ///    combination will never repeat.
  ///
  /// Failure to comply with these requirements can lead to **compromises in
  /// encryption security**, such as exposing sensitive data or enabling
  /// cryptographic attacks.
  ///
  /// Examples:
  /// ```
  /// use rand::Rng;
  /// use glyphs::crypto::Nonce;
  /// let mut rng = rand::thread_rng();
  /// let random_nonce = Nonce::<32>::from_bytes(rng.gen());
  /// ```
  pub fn from_bytes(data: [u8; N]) -> Self {
    Nonce(data)
  }

  /// Constructs a new `Nonce` with the provided random number generator.
  ///
  /// # Warning
  ///
  /// You **must** ensure that the `rng` is appropriately initialized so that
  /// the outputs are truly random, ensuring that there's no possibility of
  ///    repetition.
  ///
  /// Failure to comply with this requirement can lead to **compromises in
  /// encryption security**, such as exposing sensitive data or enabling
  /// cryptographic attacks.
  ///
  /// Examples:
  /// ```
  /// use rand::Rng;
  /// use glyphs::crypto::Nonce;
  /// let mut rng = rand::thread_rng();
  /// let random_nonce = Nonce::<32>::from_rng(rng.gen());
  /// ```
  pub fn from_rng<R: Rng + CryptoRng>(rng: &mut R) -> Self {
    let mut bytes = [0u8; N];
    rng.fill_bytes(&mut bytes);
    Self(bytes)
  }
}

impl<const N: usize> Debug for Nonce<N> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "Nonce({:?})", &ShortHexDump(&self.0[..], 0))
  }
}

pub trait GlyphsCryptographicKey: Debug + Sized + Send {
  fn key_type(&self) -> CryptoKeyTypes;

  fn fingerprint(&self) -> Sha3Hash;

  fn expires(&self) -> &DateTime;

  fn read(
    key_type: CryptoKeyTypes,
    expires: &DateTime,
    public: &[u8],
    private: &[u8],
  ) -> Result<Self, GlyphErr>;

  fn key_len_public(&self) -> usize;

  fn write_public(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>;

  fn key_len_private(&self) -> usize;

  fn write_private(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>;
}

pub trait GlyphsSigningKey: GlyphsCryptographicKey {
  type Signature: CryptoSignatureOldTrait;

  type HashContext: HashContext;

  fn sign(&self, bytes: &[u8]) -> Self::Signature;

  fn new_hash_context(&self) -> Self::HashContext;

  fn sign_pre_hashed(
    &self,
    context: Self::HashContext,
  ) -> Result<Self::Signature, CryptoErr>;
}

pub trait GlyphsAuthenticationKey: GlyphsCryptographicKey {
  type HashContext: HashContext;

  type Signature: CryptoSignatureOldTrait;

  fn verify(
    &self,
    bytes: &[u8],
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr>;

  fn new_hash_context(&self) -> Self::HashContext;

  fn verify_pre_hashed(
    &self,
    context: Self::HashContext,
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr>;
}

pub trait CryptoSignatureOldTrait:
  Debug + Sized + Send + Sync + 'static
{
  fn len(&self) -> usize;

  fn read(source: &[u8], cursor: &mut usize) -> Result<Self, GlyphErr>;

  fn write(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>;
}

pub enum SigningKeyEnum {
  Ed25519(ed25519_dalek::SigningKey),
}

pub enum VerifyingKeyEnum {
  Ed25519(ed25519_dalek::VerifyingKey),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CryptoErr {
  KeyExpired,
  KeyRevoked,
  InvalidKeyType,
  EncryptionError,
  DecryptionError,
  SignatureError,
  VerificationFailed,
  InvalidKeyMaterial,
  Aes256WrongKeyLength(usize),
  Ed25519PublicWrongKeyLength(usize),
  Ed25519InvalidKey,
  Ed25519PrivateWrongKeyLength(usize),

  SignatureVerificationFailed,
  InvalidSigningKey,
  UnsupportedKeyRead,
  /// Attempted to decode one type of cryptographic key, but the observed type
  /// did not match
  WrongKeyType {
    expected: CryptoKeyTypes,
    observed: CryptoKeyTypes,
  },
  InvalidSigningKeyType(CryptoKeyTypes),
  SignatureInvalid,
  SignatureTypeUnknown(SignatureType),
  SignatureCommentInvalid,
  InternalErrorEd25519,
}

#[cfg(test)]
pub(crate) mod test {
  use crate::{
    crypto::{
      algos::ed25519::{Ed25519PrivateKey, Ed25519PublicKey},
      CryptoKeyGlyph, CryptographicHash, GlyphHash, GlyphsCryptographicKey,
      SigningKey, SigningReason,
    },
    glyph_new, EncodedGlyph, FromGlyph,
  };
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[cfg(test)]
  pub(crate) const TEST_PLAINTEXT: &[u8; 39] =
    b"Deutsche Truppen sind jetzt in England.";

  #[test]
  fn signatures() {
    let mut rng = ChaCha20Rng::from_seed([0; 32]);
    let key = SigningKey::new_ed25519(&mut rng, None);
    std::dbg!(&key);
    let what_to_sign = GlyphHash::new(TEST_PLAINTEXT);
    let reason = SigningReason::Unspecified;
    let sig = key.sign(what_to_sign, reason, None).unwrap();
    std::dbg!(&sig);
    let valid_for = sig.valid_for().unwrap();
    assert_eq!(valid_for, key.fingerprint());

    // Altered work proof should break the sig
    let mut broken = sig.clone();
    broken.work_proof[0] ^= 0xFF;
    std::dbg!(&broken);
    assert!(broken.valid_for().is_err());

    // Altering what's signed should break the sig
    broken = sig.clone();
    broken.what_signed.0[0] ^= 0xFF;
    assert!(broken.valid_for().is_err());

    // Altering the reason should break the sig
    broken = sig.clone();
    broken.reason = SigningReason::UnknownReasonType(0xFFFE.into());
    assert!(broken.valid_for().is_err());

    // Create a signature glyph
    let sg = glyph_new(&sig).unwrap();

    todo!()

    // Test if the signature glyph is verified
  }

  #[test]
  fn crypto_codec() {
    let mut rng = ChaCha20Rng::from_seed([0; 32]);
    key_codec_ed25519(&mut rng);
  }

  #[allow(unused)]
  fn key_codec_ed25519(rng: &mut ChaCha20Rng) {
    let sk = Ed25519PrivateKey::generate(rng, None);
    let pk = sk.public_key().clone();

    // Codec for private key
    let g = glyph_new(&sk).unwrap();
    // dbg!(&skg);
    let sckg = CryptoKeyGlyph::from_glyph(g).unwrap();
    dbg!(&sckg);
    let sk_from_glyph = Ed25519PrivateKey::from_glyph(sckg.glyph()).unwrap();
    dbg!(&sk_from_glyph);
    assert_eq!(sk, sk_from_glyph);
    let sk_try_from = Ed25519PrivateKey::try_from(&sckg).unwrap();
    assert_eq!(sk, sk_try_from);
    assert_eq!(sk_from_glyph, sk_try_from);

    // Decode as a generic signing key.
    let sign_key = SigningKey::from_glyph(sckg.glyph()).unwrap();
    dbg!(&sign_key);
    let sign_key_try_from = SigningKey::try_from(&sckg).unwrap();
    dbg!(&sign_key_try_from);
    assert_eq!(sign_key, sign_key_try_from);

    // Codec for public key
    let g = glyph_new(&pk).unwrap();
    let pckg = CryptoKeyGlyph::from_glyph(g).unwrap();
    dbg!(&pckg);
    let pk_from_glyph = Ed25519PublicKey::from_glyph(pckg.glyph()).unwrap();
    dbg!(&pk_from_glyph);
    assert_eq!(pk, pk_from_glyph);
    let pk_try_from = Ed25519PublicKey::try_from(&pckg).unwrap();
    dbg!(&pk_try_from);
    assert_eq!(pk, pk_try_from);

    // Decode public key from private key
    let pk_from_glyph = Ed25519PublicKey::from_glyph(sckg.glyph()).unwrap();
    dbg!(&pk_from_glyph);
    assert_eq!(pk, pk_from_glyph);
    let pk_try_from = Ed25519PublicKey::try_from(&sckg).unwrap();
    dbg!(&pk_try_from);
    assert_eq!(pk, pk_try_from);
  }

  // fn key_codec_signing_enum(rng: &mut ChaCha20Rng) {}
}
