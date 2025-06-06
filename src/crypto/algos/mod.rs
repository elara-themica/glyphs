//! Adaptations of Cryptographic Algorithms
//!
//! # Overview
//!
//! This module contains adaptations of cryptographic algorithms for use with
//! glyphs.  The primary purpose of this module is to provide a consistent API
//! for cryptographic algorithms for the rest of this library, with public APIs
//! that can be used for third-party implementation of other cryptographic
//! algorithms.
//!
//! Initially, we implement only a small subset of the algorithms that are
//! commonly used in the cryptographic community--AES 256 for symmetric
//! encryption and Curve25519 for asymmetric encryption and digital signatures
//! using the `aes`, `ed25519-dalek` and `x25519-dalek` crates.
//!
//! - [`CryptoKey`].  This trait is implemented by all cryptographic keys, and
//!   provies
//!
//! - [`SigningKey`]
//! - [`AuthenticationKey`]
//! - [`CryptoSignature`]
//!
//!

use crate::crypto::{
  CryptoErr, CryptoKeyTypes, CryptoSignatureTypes, Sha3Hash,
};
use argon2::password_hash::rand_core::CryptoRng;
use core::fmt::Debug;
use rand::Rng;

pub(super) mod aes;
pub(super) mod ed25519;

/// Internal trait for Cryptographic Keys
pub trait CryptoKey: Debug + Sized + Send {
  type PublicBytes<'a>: AsRef<[u8]>
  where
    Self: 'a;

  type SecretBytes<'a>: AsRef<[u8]>
  where
    Self: 'a;

  /// Returns the fingerprint of this key
  fn fingerprint(&self) -> &Sha3Hash;

  /// Returns the type of this cryptographic key.
  ///
  /// This is intended to be used for serialization.
  fn key_type(&self) -> CryptoKeyTypes;

  /// The length serialized key's public component (if any), in bytes.
  fn public_len(&self) -> usize;

  /// The length serialized key's secret component (if any), in bytes.
  fn secret_len(&self) -> usize;

  /// The serialized bytes of the public key component (if any).
  fn public_bytes(&self) -> Self::PublicBytes<'_>;

  /// The serialized bytes of the private key component (if any).
  fn secret_bytes(&self) -> Self::SecretBytes<'_>;

  /// Read the serialized key from the provided buffer.
  fn deserialize(
    key_type: CryptoKeyTypes,
    public_bytes: &[u8],
    secret_bytes: &[u8],
  ) -> Result<Self, CryptoErr>;
}

pub trait GenerableCryptoKey: CryptoKey {
  fn generate<R: Rng + CryptoRng>(rng: &mut R) -> Self;
}

/// Keys used for creating digital signatures.
pub trait SigningKey: CryptoKey {
  /// The type of public key used to authenticate the signature.
  type AuthenticationKey: AuthenticationKey;

  /// The type of signature produced by this key.
  type Signature: CryptoSignature;

  /// The public key used to authenticate the signature.
  fn authentication_key(&self) -> &Self::AuthenticationKey;

  /// Produce a digital signature for the provided bytes.
  ///
  /// Note that this is distinct from the full signature provided by a
  /// [`SignatureGlyph`]; this is for the cryptographic signature only.
  fn sign(&self, bytes: &[u8]) -> Self::Signature;
}

/// Keys used to authenticate digital signatures.
pub trait AuthenticationKey: CryptoKey {
  /// The type of signature that can be verified by this key.
  type Signature: CryptoSignature;

  /// Returns `Ok(())` if the signature is valid or an `Err` otherwise.
  fn verify(
    &self,
    bytes: &[u8],
    signature: &Self::Signature,
  ) -> Result<(), CryptoErr>;
}

/// Cryptographic signatures created by a [`SigningKey`],
pub trait CryptoSignature: Sized {
  /// The type of key used to authenticate this signature.
  type AuthenticationKey: AuthenticationKey;

  type SignatureBytes<'a>: AsRef<[u8]>
  where
    Self: 'a;

  fn signature_type(&self) -> CryptoSignatureTypes;

  /// The length of the serialized signature, in bytes.
  ///
  /// The default implementation just uses the `signature_bytes()` function;
  /// this can be overridden if/when serialization is non-trivial.
  fn signature_length(&self) -> usize {
    self.signature_bytes().as_ref().len()
  }

  fn signature_bytes(&self) -> Self::SignatureBytes<'_>;

  /// Deserialize a signature from the provided buffer.
  fn deserialize(
    sig_type: CryptoSignatureTypes,
    source: &[u8],
  ) -> Result<Self, CryptoErr>;
}
