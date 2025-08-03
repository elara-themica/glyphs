//! Cryptographic Hashes, Signatures, and Ciphers
//!
//! # APIs for Use vs. Extensibility
//!
//!
//!
//! # Hash Algorithms
//!
//! A variety of cryptographic hash algorithms are supported.  The primary hash
//! for content indexing has not yet been determined, but will likely be
//! either [`SHA256`] (for its ubiquity and hardware acceleration) or [`Blake3`]
//! (for its support of parallelization).  The type alias is [`GlyphHash`].
//! [`SHA3Hash`] is used for cryptographic fingerprints due to its larger safety
//! margin.  [`SHA1Hash`] and [`MD5Hash`] are provided for backwards
//! compatibility.  Other hashes may be added in the future for broader
//! application support.
//!
//! Cryptographic hashes are quasi-serialized into the [`HashGlyph`] type, with
//! type IDs of different hash algorithms from the [`CryptoHashType`] `enum`.
//!
//! # Cryptographic Keys
//!
//! The initial version of Glyphs includes implementation for only a few types
//! of cryptographic keys--namely, AES-256 ([`AesKey`]) for symmetric
//! cryptography, Ed25519 ([`Ed25519PublicKey`] and [`Ed25519SecretKey`]) for
//! authentication, and X25519 for public key cryptography.
//!
//! Cryptographic keys are serialized into the [`CryptoKeyGlyph`] type, with
//! key type identifiers found in the [`CryptoKeyTypes`] `enum`. Unlike most
//! other glyph types, we make no effort to provide functional zero-copy access
//! to cryptographic functions through this type.
//!
//! # Cryptographic Signatures
//!
//! The initial version of Glyphs only includes native support for cryptographic
//! signatures using Ed25519 ([`Ed25519Signature`]), quasi-serialized into a
//! [`SignatureGlyph`].  Signatures in Glyphs are over metadata that includes
//! (1) a cryptographic hash of the signed data, (2) a reason for that signature
//! ([`SigningReason`]), (3) an optional "Signing Statement" glyph that provides
//! arbitrary additional information, and (4) a 16-byte proof-of-work [`Nonce`].
//!
//! In addition, signature glyphs include a serialized copy of the public key
//! necessary to validate the signature, allowing verification without separate
//! access to that public key.

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

use crate::{
  crypto::algos::{CryptoKey, GenerableCryptoKey},
  misc::DateTime,
  util::debug::ShortHexDump,
  zerocopy::{BufferErr, U16},
  GlyphErr,
};
use core::{
  fmt::{Debug, Formatter},
  mem::transmute,
};
use rand::{CryptoRng, Rng};

pub struct Key<C: CryptoKey> {
  key:     C,
  expires: DateTime,
}

impl<C: CryptoKey> Key<C>
where
  C: GenerableCryptoKey,
{
  pub fn generate<R: Rng + CryptoRng>(
    rng: &mut R,
    expires: Option<DateTime>,
  ) -> Result<Self, GlyphErr> {
    let key = C::generate(rng);
    let expires = expires.unwrap_or(DateTime::NEVER);
    Ok(Self { key, expires })
  }
}

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
  /// let random_nonce = Nonce::<32>::from_rng(&mut rng);
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

impl<const N: usize> AsRef<[u8]> for Nonce<N> {
  fn as_ref(&self) -> &[u8] {
    self.0.as_ref()
  }
}

/// Identifies the type of cryptographic signature used.
// SAFETY: (1) All values must be contiguous, and (2) `Unknown` must be highest.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum CryptoSignatureTypes {
  Ed25519 = 0x0000,
  // When adding additional signature types, make sure to update the `From<u16>`
  // to reflect the new highest ID.
  Unknown = 0xFFFF,
}

impl From<u16> for CryptoSignatureTypes {
  fn from(value: u16) -> Self {
    if value > CryptoSignatureTypes::Ed25519 as u16 {
      CryptoSignatureTypes::Unknown
    } else {
      unsafe { transmute::<u16, CryptoSignatureTypes>(value) }
    }
  }
}

impl From<U16> for CryptoSignatureTypes {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<CryptoSignatureTypes> for u16 {
  fn from(value: CryptoSignatureTypes) -> Self {
    value as u16
  }
}

impl From<CryptoSignatureTypes> for U16 {
  fn from(value: CryptoSignatureTypes) -> Self {
    (value as u16).into()
  }
}

/// An enumeration of reasons for providing a cryptographic signature.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
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

/// A list of cryptographic key types and corresponding type ids.
//
// SAFETY:  Updating this?  Remember to keep the list and IDs contiguous and
// update the `From<u16>` implementation below with the highest ID.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum CryptoKeyTypes {
  /// The type of the key is deliberately unspecified.
  Unspecified = 0x0000,
  /// A 256-bit AES key
  Aes256 = 0x0001,
  /// An Ed25519 Public Key
  Ed25519Public = 0x0002,
  /// An Ed25519 Private Key
  Ed25519Private = 0x0003,
  /// An X25519 Public Key
  X25519Public = 0x0004,
  /// An X25519 Private Key
  X25519Private = 0x0005,
  /// An unknown key type.
  Unknown = 0x0006,
}

impl From<u16> for CryptoKeyTypes {
  fn from(type_id: u16) -> Self {
    if type_id > CryptoKeyTypes::Unknown as u16 {
      CryptoKeyTypes::Unknown
    } else {
      // SAFETY: Depends on highest known ID being checked, safety note
      // left in that code.
      unsafe { transmute::<u16, Self>(type_id) }
    }
  }
}

impl From<U16> for CryptoKeyTypes {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<CryptoKeyTypes> for U16 {
  fn from(value: CryptoKeyTypes) -> Self {
    U16::from(value as u16)
  }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CryptoErr {
  BufferOutOfBounds {
    index:  usize,
    length: usize,
  },
  /// When decoding a key, the stored fingerprint did not match the calculated
  /// fingerprint of the key.
  ///
  /// Only the last 4 bytes of the fingerprint are provided, as this keeps the
  /// error type small (two full hashes would take 64 bytes) and the chance of
  /// a collision is still one in 2^32.
  FingerprintMismatch {
    calculated: [u8; 4],
    stored:     [u8; 4],
  },
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
  WrongSignatureType {
    expected: CryptoSignatureTypes,
    observed: CryptoSignatureTypes,
  },
  InvalidSigningKeyType(CryptoKeyTypes),
  SignatureInvalid,
  SignatureTypeUnknown(u16),
  SignatureCommentInvalid,
  InternalErrorEd25519,
}

impl From<BufferErr> for CryptoErr {
  fn from(value: BufferErr) -> Self {
    match value {
      BufferErr::OutOfBounds { index, length } => {
        CryptoErr::BufferOutOfBounds { index, length }
      },
    }
  }
}

#[inline]
fn verify_fingerprint(
  calculated: &Sha3Hash,
  stored: &Sha3Hash,
) -> Result<(), CryptoErr> {
  if calculated != stored {
    Err(CryptoErr::FingerprintMismatch {
      calculated: calculated.suffix_bytes(),
      stored:     stored.suffix_bytes(),
    })
  } else {
    Ok(())
  }
}
