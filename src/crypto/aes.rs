//! GLIFS interface for AES encryption, using the `aes_ctr` crate and re-using
//! the already-needed [`GlifsHash`] for integrity verification.
use crate::{
  crypto::{
    Blake3Hash, CiphertextMetadata, CiphertextMetadataInner, CryptoErr,
    CryptographicHash, DecryptionKey, EncryptionKey, EncryptionSchemes,
    FingerprintKey, GlyphHash, Sha3Hash,
  },
  util::debug::ShortHexDump,
  zerocopy::ZeroCopy,
  GlyphErr,
};
use aes::cipher::{KeyIvInit, StreamCipher};
use core::{
  convert::TryFrom,
  fmt::{Debug, Formatter},
  mem::size_of,
};
use rand::{CryptoRng, RngCore};

/// The size of an AES block (independent of key length).
pub(crate) const AES_BLOCK_SIZE: usize = 16;

type Aes256Ctr = ctr::Ctr128LE<::aes::Aes256>;

/// An AES Key.
///
/// The development version of GLIFS uses only AES-256 in CTR mode.
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(C)]
pub struct AesKey([u8; 32]);

impl AesKey {
  /// Generate a new random AES key
  pub fn new<R>(mut rng: R) -> AesKey
  where
    R: RngCore + CryptoRng,
  {
    let mut key = AesKey([0u8; 32]);
    rng.fill_bytes(&mut key.0[..]);
    key
  }

  /// Returns the bytes of the key as a byte slice.
  ///
  /// If you need convert to/from a fixed length array, use the provided `From`
  /// implementation.
  pub fn bytes(&self) -> &[u8] {
    &self.0[..]
  }

  /// Creates a new key from a 32-byte byte slice (256-bit key).
  pub fn from_bytes(bytes: &[u8]) -> Result<AesKey, GlyphErr> {
    if bytes.len() != 32 {
      Err(err!(trace, GlyphErr::CryptoKeyLength))
    } else {
      let mut key_bytes = [0u8; 32];
      key_bytes.clone_from_slice(bytes);
      Ok(AesKey(key_bytes))
    }
  }
}

impl FingerprintKey for AesKey {
  fn key_fingerprint(&self) -> Sha3Hash {
    Sha3Hash::new(&self.0[..])
  }
}

impl From<[u8; 32]> for AesKey {
  fn from(src: [u8; 32]) -> Self {
    AesKey(src)
  }
}

impl From<AesKey> for [u8; 32] {
  fn from(src: AesKey) -> Self {
    src.0
  }
}

impl TryFrom<&[u8]> for AesKey {
  type Error = CryptoErr;

  fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
    if value.len() == 32 {
      let mut key_bytes = [0u8; 32];
      key_bytes.clone_from_slice(value);
      Ok(AesKey(key_bytes))
    } else {
      Err(err!(trace, CryptoErr::KeyLength))
    }
  }
}

impl Debug for AesKey {
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "AesKey({:?})", ShortHexDump(&self.0[..], 4))?;
    Ok(())
  }
}

/// An AES initialization vector.
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(packed)]
pub struct AesIv([u8; AES_BLOCK_SIZE]);

unsafe impl ZeroCopy for AesIv {}

/// An AES Nonce
impl AesIv {
  // const AES_NONCE_LEN: usize = 12;

  /// Generate a new random IV
  pub fn new<R>(mut rng: R) -> AesIv
  where
    R: RngCore + CryptoRng,
  {
    let mut iv = AesIv([0u8; AES_BLOCK_SIZE]);
    rng.fill_bytes(&mut iv.0[..]);
    iv
  }

  /// Generates an IV based on hashing an ephemeral key.
  ///
  /// Take care that this function is not used with a static (predictable) key,
  /// such as those based on passwords, as this enabled a variety of
  /// cryptographic attacks.
  pub fn from_ephemeral_key(key: &AesKey) -> AesIv {
    let key_hash = Blake3Hash::new(key.bytes());
    let mut iv = AesIv([0u8; AES_BLOCK_SIZE]);
    iv.0[..].clone_from_slice(&key_hash.hash_bytes()[0..AES_BLOCK_SIZE]);
    iv
  }

  /// The contents of the initialization vector, as a slice of 16 bytes.
  pub fn bytes(&self) -> &[u8] {
    &self.0[..]
  }

  /// Return a new AesIv for CTR mode advanced by `offset` bytes.
  pub fn ctr_offset(&self, offset: i64) -> Self {
    let mut value = i128::from_be_bytes(self.0);
    value += i128::from(offset);
    AesIv(value.to_be_bytes())
  }
}

impl Debug for AesIv {
  fn fmt(&self, f: &mut Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "AesIV({:?})", ShortHexDump(&self.0[..], 4))?;
    Ok(())
  }
}

impl EncryptionKey for AesKey {
  fn metadata_glyph_len(&self) -> usize {
    CiphertextMetadata::glyph_len(EncryptionSchemes::Aes256Ctr)
  }

  fn encrypt<R: RngCore + CryptoRng>(
    &self,
    rng: R,
    data: &mut [u8],
  ) -> Result<(GlyphHash, CiphertextMetadata), GlyphErr> {
    let iv = AesIv::new(rng);
    let (hash, mac) = aes_256ctr_encrypt(self, &iv, data);
    let cm = CiphertextMetadata::new_aes_256(self.key_fingerprint(), iv, mac);
    Ok((hash, cm))
  }
}

impl DecryptionKey for AesKey {
  fn decrypt(
    &self,
    metadata: &CiphertextMetadata,
    data: &mut [u8],
  ) -> Result<GlyphHash, GlyphErr> {
    if let CiphertextMetadataInner::Aes256Ctr { iv, mac } = &metadata.inner {
      aes_256ctr_decrypt(self, iv, mac, data)
    } else {
      Err(err!(debug, GlyphErr::WrongCryptoScheme))
    }
  }
}

/// Common AES-256 encryption function.
///
/// Encrypts data in place, returns the hash of the plaintext and an [`AesMac`].
pub fn aes_256ctr_encrypt(
  key: &AesKey,
  iv: &AesIv,
  data: &mut [u8],
) -> (GlyphHash, AesMac) {
  let hash = GlyphHash::new(data);
  let mut crypter = Aes256Ctr::new(key.bytes().into(), iv.bytes().into());
  crypter.apply_keystream(data);
  let mut mac = AesMac(*hash.hash_bytes());
  crypter.apply_keystream(&mut mac.0[..]);
  (hash, mac)
}

/// Common AES-256 decryption function.
///
/// Decrypts the data in place.  Returns an error if the ciphertext is invalid,
/// in which case `data` will then contain the invalid plaintext.
#[inline]
pub fn aes_256ctr_decrypt(
  key: &AesKey,
  iv: &AesIv,
  stored_mac: &AesMac,
  data: &mut [u8],
) -> Result<GlyphHash, GlyphErr> {
  let mut crypter = Aes256Ctr::new(key.bytes().into(), iv.bytes().into());
  crypter.apply_keystream(data);
  let mut decrypted_mac = *stored_mac;
  crypter.apply_keystream(&mut decrypted_mac.0[..]);
  let mac_hash = GlyphHash::from_hash_bytes(decrypted_mac.0);
  let calc_hash = GlyphHash::new(data);
  if calc_hash.eq(&mac_hash) {
    Ok(mac_hash)
  } else {
    Err(err!(trace, GlyphErr::CiphertextInvalid))
  }
}

/// A custom message authentication code based on the encrypted [`GlifsHash`] of
/// the plaintext (MAC-then-Encrypt).
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(packed)]
pub struct AesMac(pub(crate) [u8; size_of::<GlyphHash>()]);

/// SAFETY: Byte arrays are inherently zero copy
unsafe impl ZeroCopy for AesMac {}

impl From<GlyphHash> for AesMac {
  fn from(src: GlyphHash) -> Self {
    AesMac(*src.hash_bytes())
  }
}

impl Debug for AesMac {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "AesMac({:?})", &ShortHexDump(&self.0[..], 4))
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{crypto::TEST_PLAINTEXT, util::init_test_logger, GlyphErr};
  use ::test::Bencher;
  use alloc::vec::Vec;
  use rand::rngs::OsRng;
  use std::{dbg, println};

  #[test]
  fn aes_crypt() -> Result<(), GlyphErr> {
    init_test_logger();
    let mut buffer = Vec::from(&TEST_PLAINTEXT[..]);

    let mut rng = OsRng::default();
    let key = AesKey::new(&mut rng);
    let iv = AesIv::new(&mut rng);
    dbg!(&key, &iv);

    println!("Plaintext: {:?}", ShortHexDump(buffer.as_slice(), 4));

    let (enc_hash, mac) = aes_256ctr_encrypt(&key, &iv, &mut buffer[..]);
    println!("Ciphertext: {:?}", ShortHexDump(buffer.as_slice(), 4));
    dbg!(&enc_hash, &mac);
    assert_ne!(&buffer[..], &TEST_PLAINTEXT[..]);

    let dec_hash = aes_256ctr_decrypt(&key, &iv, &mac, &mut buffer[..])?;
    println!("Plaintext: {:?}", ShortHexDump(buffer.as_slice(), 4));

    assert_eq!(enc_hash, dec_hash);
    assert_eq!(&buffer[..], &TEST_PLAINTEXT[..]);

    Ok(())
  }

  #[cfg(feature = "crypto")]
  #[bench]
  fn bench_aes_ctr(b: &mut Bencher) -> Result<(), CryptoErr> {
    init_test_logger();

    let mut data = [0u8; 8192];

    let mut rng = OsRng::default();
    let key = AesKey::new(&mut rng);
    let iv = AesIv::from_ephemeral_key(&key);

    b.bytes = 8192;
    b.iter(|| {
      aes_256ctr_encrypt(&key, &iv, &mut data);
    });

    Ok(())
  }
}
