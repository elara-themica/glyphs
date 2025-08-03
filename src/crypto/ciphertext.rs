//! Encrypted glyphs and extents.
//!
//!

use crate::{
  crypto::{
    aes_256ctr_decrypt, aes_256ctr_encrypt, AesIv, AesKey, AesMac,
    CryptographicHash, GlyphHash, Nonce, Sha3Hash,
  },
  zerocopy::{ZeroCopy, U16},
  DecodeErr, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph,
};
use rand::{CryptoRng, Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::ops::Deref;

pub(super) const X25519_KEY_LEN: usize = 32;

#[derive(Copy, Clone)]
struct CiphertextHeader {
  version:           u8,
  flags:             u8,
  encryption_scheme: U16,
  metadata_len:      U16,
  reserved:          [u8; 2],
}

unsafe impl ZeroCopy for CiphertextHeader {}

impl CiphertextHeader {
  const FLAG_KEY_FINGERPRINT: u8 = 0b0000_0001;
  const VERSION_EXPERIMENTAL: u8 = 0x00;
}

// SAFETY: The `Unknown` variant must always have the highest number,
//         and lesser values must indicate a valid variant.
#[repr(u16)]
pub enum EncryptionScheme {
  AesCtr = 0x0000,
  X25519Ctr = 0x0001,
  Unknown = 0x0002,
}

impl EncryptionScheme {
  pub fn metadata_len(&self) -> usize {
    match self {
      EncryptionScheme::AesCtr => size_of::<AesIv>() + size_of::<AesMac>(),
      EncryptionScheme::X25519Ctr => {
        size_of::<x25519_dalek::PublicKey>() + size_of::<AesMac>()
      },
      EncryptionScheme::Unknown => 0,
    }
  }
}

impl From<u16> for EncryptionScheme {
  fn from(value: u16) -> Self {
    if value >= EncryptionScheme::Unknown as u16 {
      EncryptionScheme::Unknown
    } else {
      // SAFETY: Limited to valid values.
      unsafe { core::mem::transmute(value) }
    }
  }
}

impl From<U16> for EncryptionScheme {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<EncryptionScheme> for u16 {
  fn from(value: EncryptionScheme) -> Self {
    value as u16
  }
}

impl From<EncryptionScheme> for U16 {
  fn from(value: EncryptionScheme) -> Self {
    (value as u16).into()
  }
}

/// Metadata necessary for decryption (e.g., ephemeral keys, MACs, etc...)
pub(crate) enum CiphertextMetadata {
  /// The ciphertext was encrypted using an AES-256 key directly.
  Aes256Ctr {
    /// The initialization value for the key stream
    iv:  AesIv,
    /// The message authentication code
    mac: AesMac,
  },
  /// The ciphertext was encrypted with a X25519 key with a known fingerprint.
  X25519Aes256Ctr {
    /// The ephemeral public key for diffie-hellman
    eph_pk: [u8; X25519_KEY_LEN],
    /// The message authentication code
    mac:    AesMac,
  },
  Unknown,
}

impl CiphertextMetadata {
  pub fn read(
    from: &[u8],
    cursor: &mut usize,
    scheme: EncryptionScheme,
  ) -> Result<Self, GlyphErr> {
    match scheme {
      EncryptionScheme::AesCtr => {
        let iv = AesIv::bbrd(from, cursor)?;
        let mac = AesMac::bbrd(from, cursor)?;
        Ok(Self::Aes256Ctr { iv, mac })
      },
      EncryptionScheme::X25519Ctr => {
        let eph_pk: [u8; X25519_KEY_LEN] = u8::bbrda(from, cursor)?;
        let mac = AesMac::bbrd(from, cursor)?;
        Ok(Self::X25519Aes256Ctr { eph_pk, mac })
      },
      EncryptionScheme::Unknown => Ok(Self::Unknown),
    }
  }

  pub fn write(
    &self,
    to: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    match self {
      CiphertextMetadata::Aes256Ctr { iv, mac } => {
        iv.bbwr(to, cursor)?;
        mac.bbwr(to, cursor)?;
        Ok(())
      },
      CiphertextMetadata::X25519Aes256Ctr { eph_pk, mac } => {
        u8::bbwrs(&eph_pk[..], to, cursor)?;
        mac.bbwr(to, cursor)?;
        Ok(())
      },
      CiphertextMetadata::Unknown => Ok(()),
    }
  }
}

pub struct EncryptedGlyph<G: Deref<Target = Glyph>> {
  glyph:      G,
  metadata:   CiphertextMetadata,
  ciphertext: *const [u8],
}

impl<G: Deref<Target = Glyph>> EncryptedGlyph<G> {
  pub fn decrypt(
    &self,
    _key: DecryptionKey,
  ) -> Result<alloc::boxed::Box<Glyph>, GlyphErr> {
    todo!()
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for EncryptedGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, GlyphErr>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Vec) {
      return Err(DecodeErr::new(source, err));
    }
    let contents = source.content_padded();
    let mut cursor = 0;
    let header = match CiphertextHeader::bbrd(&contents, &mut cursor) {
      Ok(header) => header,
      Err(err) => return Err(DecodeErr::new(source, err.into())),
    };
    let scheme: EncryptionScheme = header.encryption_scheme.get().into();
    let metadata = match CiphertextMetadata::read(contents, &mut cursor, scheme)
    {
      Ok(metadata) => metadata,
      Err(err) => return Err(DecodeErr::new(source, err)),
    };
    let ciphertext = u8::bbrfs_i(contents, &mut cursor) as *const [u8];
    Ok(Self {
      glyph: source,
      metadata,
      ciphertext,
    })
  }
}

pub struct EncryptedExtent<G: Deref<Target = Glyph>> {
  glyph: G,
}

pub struct GlyphCrypter<G: ToGlyph> {
  glyph:                G,
  key:                  EncryptionKey,
  nonce:                Nonce<32>,
  disclose_fingerprint: bool,
}

impl<G: ToGlyph> GlyphCrypter<G> {
  pub fn new(
    glyph: G,
    key: EncryptionKey,
    nonce: Nonce<32>,
    disclose_fingerprint: bool,
  ) -> Self {
    Self {
      glyph,
      key,
      nonce,
      disclose_fingerprint,
    }
  }
}

impl<G: ToGlyph> ToGlyph for GlyphCrypter<G> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let encryption_scheme = self.key.encryption_scheme();
    let metadata_len = encryption_scheme.metadata_len();
    debug_assert_eq!(metadata_len % 8, 0);

    GlyphHeader::new(
      GlyphType::EncryptedGlyph,
      self.glyph_len().saturating_sub(size_of::<GlyphHeader>()),
    )?
    .bbwr(target, cursor)?;
    CiphertextHeader {
      version:           0,
      flags:             0,
      encryption_scheme: encryption_scheme.into(),
      metadata_len:      metadata_len.try_into()?,
      reserved:          Default::default(),
    }
    .bbwr(target, cursor)?;
    let mut metadata_cursor = *cursor;
    *cursor += metadata_len;
    let mut data_cursor = *cursor;
    self.glyph.glyph_encode(target, &mut data_cursor)?;
    let metadata = self
      .key
      .encrypt(&self.nonce, &mut target[metadata_cursor..data_cursor])?;
    metadata.write(target, &mut metadata_cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<CiphertextHeader>()
      + self.key.encryption_scheme().metadata_len()
      + self.glyph.glyph_len()
  }
}

pub enum EncryptionKey {
  Aes256(AesKey),
  X25519(x25519_dalek::PublicKey),
}

impl EncryptionKey {
  pub fn gen_aes256<R: Rng + CryptoRng>(rng: &mut R) -> Self {
    let key = AesKey::new(rng);
    Self::Aes256(key)
  }

  pub(crate) fn encrypt(
    &self,
    nonce: &Nonce<32>,
    data: &mut [u8],
  ) -> Result<CiphertextMetadata, GlyphErr> {
    let mut rng = ChaCha20Rng::from_seed(nonce.0);
    match self {
      EncryptionKey::Aes256(key) => {
        let iv = AesIv::new_random(&mut rng);
        let (_hash, mac) = aes_256ctr_encrypt(key, &iv, data);
        let metadata = CiphertextMetadata::Aes256Ctr { iv, mac };
        Ok(metadata)
      },
      EncryptionKey::X25519(target_pk) => {
        let eph_sk = ::x25519_dalek::EphemeralSecret::random_from_rng(&mut rng);
        let eph_pk = ::x25519_dalek::PublicKey::from(&eph_sk);
        let ss = eph_sk.diffie_hellman(target_pk);

        let ss_hash = Sha3Hash::new(ss.as_bytes());
        let ss_key = AesKey::from_bytes(&ss_hash.hash_bytes()[..])?;
        let iv = AesIv::from_ephemeral_key(&ss_key);

        let (_hash, mac) = aes_256ctr_encrypt(&ss_key, &iv, data);
        let metadata = CiphertextMetadata::X25519Aes256Ctr {
          eph_pk: eph_pk.to_bytes(),
          mac,
        };
        Ok(metadata)
      },
    }
  }

  pub(crate) fn encryption_scheme(&self) -> EncryptionScheme {
    match self {
      EncryptionKey::Aes256(_) => EncryptionScheme::AesCtr,
      EncryptionKey::X25519(_) => EncryptionScheme::X25519Ctr,
    }
  }
}

pub enum DecryptionKey {
  Aes256(AesKey),
  X25519(x25519_dalek::StaticSecret),
}

impl DecryptionKey {
  pub fn gen_aes256<R: Rng + CryptoRng>(_rng: &mut R) -> Self {
    todo!()
  }

  pub(crate) fn decrypt(
    &self,
    metadata: &CiphertextMetadata,
    data: &mut [u8],
  ) -> Result<GlyphHash, GlyphErr> {
    match (self, metadata) {
      (Self::Aes256(key), CiphertextMetadata::Aes256Ctr { iv, mac }) => {
        aes_256ctr_decrypt(key, iv, mac, data)
      },
      (
        Self::X25519(sk),
        CiphertextMetadata::X25519Aes256Ctr { eph_pk, mac },
      ) => {
        let eph_pk = x25519_dalek::PublicKey::from(*eph_pk);
        let ss = sk.diffie_hellman(&eph_pk);
        let ss_hash = Sha3Hash::new(ss.as_bytes());
        let key = AesKey::from_bytes(&ss_hash.hash_bytes()[..])?;
        let iv = AesIv::from_ephemeral_key(&key);
        aes_256ctr_decrypt(&key, &iv, mac, data)
      },
      (_, _) => Err(GlyphErr::WrongCryptoScheme),
    }
  }
}

impl From<EncryptionKey> for DecryptionKey {
  fn from(_value: EncryptionKey) -> Self {
    todo!()
  }
}

// #[cfg(test)]
// mod tests {
//   use super::*;
//   use crate::{
//     crypto::{test::TEST_PLAINTEXT, CryptoKeyGlyph},
//     glyph_new,
//   };
//   use std::dbg;
//
//   #[test]
//   fn ciphertext() {
//     todo!()
//     // let mut rng = ChaCha20Rng::from_seed([0; 32]);
//     // let key =
//     //   CryptoKeyGlyph::gen_ed25519_private(&mut rng, None, None).unwrap();
//     // dbg!(&key);
//     //
//     // let secret_message = core::str::from_utf8(TEST_PLAINTEXT).unwrap();
//     // let secret_message = glyph_new(secret_message).unwrap();
//     // dbg!(&secret_message);
//     // let crypter = Glyph
//   }
// }
