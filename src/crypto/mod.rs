//! Types for Cryptographic Hashes, Keys, Signatures, and Ciphertext.

mod aes;
pub use self::aes::*;

mod ciphertext;
pub use self::ciphertext::*;

mod ed25519;
pub use self::ed25519::*;

mod hash;
pub use hash::*;

#[cfg(feature = "md5")]
pub use hash::md5::*;

#[cfg(feature = "sha1")]
pub use hash::sha1::*;

#[cfg(feature = "sha2")]
pub use hash::sha2::*;

#[cfg(feature = "sha3")]
pub use hash::sha3::*;

#[cfg(feature = "blake3")]
pub use hash::blake3::*;

mod keys;
pub use self::keys::*;

mod password;
pub use self::password::*;

mod sign;
pub use self::sign::*;

mod x25519;
pub use self::x25519::*;

/// Common plaintext to use for tests, based on an example Turing used at
/// Bletchley Park.
#[cfg(test)]
pub(crate) const TEST_PLAINTEXT: &[u8; 39] =
  b"Deutsche Truppen sind jetzt in England.";

/// Errors that may occur while working with cryptographic functions.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u32)]
pub enum CryptoErr {
  /// An attempt was made to write/export some value that was marked as not
  /// writable (e.g., a private key without a passphrase).
  WritingForbidden,

  /// A function expected to see one type of key type, but observed another.
  UnexpectedKeyType,

  /// A decryption operation was attempted for something that was already
  /// known to be decrypted.
  AlreadyDecrypted,

  /// An operation was attempted that, e.g., requires a private key to be
  /// decrypted first.
  DecryptionNeeded,

  /// A password was required, but it was not correct.
  WrongPassword,

  /// A specific key was required, and the one provided does not match.
  WrongKey,

  /// A key was provided that did not have the correct number of bytes for the
  /// encryption used.
  KeyLength,

  /// Bytes could not be written to a closed cyphertext.
  SessionClosed,

  /// A nonce was required for this operation but none was specified.
  NonceRequired,

  /// A generic error for an unsupported operation.
  UnsupportedOperation,

  /// A type of key disclosure was requested that is not supported for this type
  /// of cryptographic key.
  ///
  /// E.g., A [`PasswordKey`] allow disclosures of a salted password hash, but,
  /// unlike with [`SigningKey`], there is no public component of the key to
  /// disclose.
  UnsupportedKeyDisclosure,

  /// A cryptographic signature is the wrong type.
  ///
  /// Probably because it was generated by a different kind of key.
  UnexpectedSigType,

  /// Some data was corrupt.
  ///
  /// E.g., bytes that were supposed to represent a signature could not be
  /// so decoded.
  CorruptData,

  /// A decoding failed, because the target fingerprint does not match.
  FingerprintMismatch,

  /// Attempt to use AES CTR offset not at a block boundary.
  UnalignedOffset,

  /// E.g., attempt to decrypt a ciphertext encoded with one scheme (e.g., to
  /// an X25519 public key) using some other scheme (e.g., a password).
  WrongScheme,

  /// An internal error, indicating a bug or an unknown error condition.
  Internal,

  /// The ciphertext length was invalid, e.g., shorter than necessary to include
  /// necessary metadata.
  CiphertextLength,

  /// The ciphertext failed authentication.
  CiphertextInvalid,

  /// Key cannot be locked without armor.
  NoArmor,

  /// Signatures Error
  Ed25519Error,

  /// Invalid Signature
  SignatureInvalid,

  /// Invalid RSA Operation/data
  RsaError,

  /// An operation was attempted on a key, but the private component of the key
  /// was still encrypted.
  // FIXUP: Update implementers of `LockedKey` to use this instead.
  KeyLocked,
}

// impl From<InvalidKeyNonceLength> for CryptoErr {
//   fn from(_src: InvalidKeyNonceLength) -> Self {
//     CryptoErr::Internal
//   }
// }
//
// impl From<::ed25519_dalek::SignatureError> for CryptoErr {
//   fn from(_src: SignatureError) -> Self {
//     CryptoErr::Ed25519Error
//   }
// }
//
// impl From<::rsa::errors::Error> for CryptoErr {
//   fn from(_src: Error) -> Self {
//     CryptoErr::RsaError
//   }
// }
