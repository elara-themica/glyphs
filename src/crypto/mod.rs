mod aes;
pub use self::aes::*;

mod sign;
pub use self::sign::*;

mod hash;
pub use self::hash::*;

#[cfg(feature = "md5")]
pub use crate::crypto::hash::md5::*;

#[cfg(feature = "sha1")]
pub use crate::crypto::hash::sha1::*;

#[cfg(feature = "sha2")]
pub use crate::crypto::hash::sha2::*;

#[cfg(feature = "sha3")]
pub use crate::crypto::hash::sha3::*;

#[cfg(feature = "blake3")]
pub use crate::crypto::hash::blake3::*;

mod keys;
pub use self::keys::*;

mod password;
pub use self::password::*;

#[cfg(test)]
pub(crate) const TEST_PLAINTEXT: &[u8; 39] =
  b"Deutsche Truppen sind jetzt in England.";

/// A number used once (for cryptography).
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
  /// let mut rng = rand::thread_rng();
  /// let random_nonce = Nonce::new(rng.gen());
  /// ```
  pub fn new_promise(data: [u8; N]) -> Self {
    Nonce(data)
  }
}

pub trait GlyphVerifier {}

pub trait GlyphEncryptor {}

pub trait GlyphDecryptor {}

#[derive(Debug)]
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
  UnsupportedCryptoScheme(CryptoKeyTypes),
  Ed25519PublicWrongKeyLength(usize),
  Ed25519InvalidKey,
  Ed25519PrivateWrongKeyLength(usize),

  /// This key type does not support creating cryptographic signatures.
  UnsupportedSigningKey(CryptoKeyTypes),
}
