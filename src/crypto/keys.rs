//! Code that is common for all types of cryptographic keys.

//! Generic types for cryptographic keys, e.g., traits for performing
//! decryption and generating signatures.
use crate::{
  crypto::{
    CiphertextMetadata, CryptoSignature, CryptoSignatureTypes, GlyphHash,
    Sha3Hash,
  },
  glyph::GlyphErr,
  zerocopy::{ZeroCopy, U16, U32},
};
use core::mem::transmute;
use rand::{CryptoRng, RngCore};

pub type KeyFingerprint = Sha3Hash;

/// A key that has a [`GlifsHash`] fingerprint--the hash of its public
/// component.
pub trait FingerprintKey {
  /// Returns the key pair's "fingerprint"; a hash of its public component.
  fn key_fingerprint(&self) -> KeyFingerprint;
}

/// A key capable of performing encryption
pub trait EncryptionKey {
  /// Returns the length of a [`CiphertextMetadata`] glyph capable of containing
  /// the information for this key, given the specified [`KeyDisclosure`] level.
  fn metadata_glyph_len(&self) -> usize;

  /// Uses the key to encrypt a block of data, returning the [`GlifsHash`] of
  /// the plaintext and the [`CiphertextMetadata`] necessary to perform the
  /// decryption.
  fn encrypt<R: RngCore + CryptoRng>(
    &self,
    rng: R,
    data: &mut [u8],
  ) -> Result<(GlyphHash, CiphertextMetadata), GlyphErr>;
}

/// A key capable of performing decryption
pub trait DecryptionKey {
  /// Given its associated metadata, decrypt the contents of `data` in place,
  /// returning the [`GlifsHash`] of the plaintext if successful.
  fn decrypt(
    &self,
    metadata: &CiphertextMetadata,
    data: &mut [u8],
  ) -> Result<GlyphHash, GlyphErr>;
}

/// A key capable of generating a cryptographic signature
pub trait SigningKey {
  /// Creates a [`CryptoSignature`] for the provided `message`
  fn sign(&self, message: &[u8]) -> Result<CryptoSignature, GlyphErr>;

  fn crypto_sig_type(&self) -> CryptoSignatureTypes;
}

// impl<T> SigningKey for T
// where
//   T: Deref,
//   T::Target: SigningKey,
// {
//   fn sign(&self, message: &[u8]) -> Result<CryptoSignature, GlyphErr> {
//     (*self).sign(message)
//   }
//
//   fn crypto_sig_type(&self) -> CryptoSignatureTypes {
//     (*self).crypto_sig_type()
//   }
// }

/// A key capable of verifying a cryptographic signature (e.g., the public key)
pub trait AuthenticationKey: FingerprintKey {
  /// Returns `true` iff the `signature` is valid for `message`.
  fn verify(&self, message: &[u8], signature: &CryptoSignature) -> bool;
}

/// A list of cryptographic key types and corresponding type ids.
//
// SAFETY:  Updating this?  Remember to keep the list and IDs contiguous and
// update the `From<u16>` implementation below with the highest ID.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum CryptoKeyTypes {
  Unknown = 0x0000,
  Aes256 = 0x0001,
  Argon2Password = 0x0002,
  Ed25519Public = 0x0003,
  Ed25519Private = 0x0004,
  Ed25519KeyPair = 0x0005,
  X25519Public = 0x0006,
  X25519Private = 0x0007,
  X25519KeyPair = 0x0008,
}

impl From<u16> for CryptoKeyTypes {
  fn from(type_id: u16) -> Self {
    if type_id > CryptoKeyTypes::X25519KeyPair as u16 {
      CryptoKeyTypes::Unknown
    } else {
      // SAFETY: Depends on highest known ID being checked, safety note
      // left in that code.
      unsafe { transmute::<u16, Self>(type_id) }
    }
  }
}

/// A common header used when encoding different types of cryptographic keys.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
pub struct CryptoKeyHeader {
  version:    u8,
  _reserved1: u8,
  type_id:    U16,
  _reserved2: U32,
}

unsafe impl ZeroCopy for CryptoKeyHeader {}

impl CryptoKeyHeader {
  pub fn new(key_type: CryptoKeyTypes) -> Self {
    Self {
      version:    0,
      _reserved1: 0,
      type_id:    U16::from(key_type as u16),
      _reserved2: Default::default(),
    }
  }

  pub fn key_type(&self) -> CryptoKeyTypes {
    CryptoKeyTypes::from(u16::from(self.type_id))
  }

  pub fn confirm_type(&self, key_type: CryptoKeyTypes) -> Result<(), GlyphErr> {
    if key_type as u16 == u16::from(self.type_id) {
      Ok(())
    } else {
      Err(err!(debug, GlyphErr::CryptoKeyType))
    }
  }
}
