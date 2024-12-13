//! Glyph types for working with encrypted data.
use crate::{
  crypto::{
    x25519::X25519_KEY_LEN, AesIv, AesMac, DecryptionKey, EncryptionKey,
    GlyphHash, Sha3Hash,
  },
  glyph::{
    glyph_close, glyph_read, FromGlyph, Glyph, GlyphErr, GlyphHeader,
    GlyphType, ToGlyph,
  },
  util::debug::ShortHexDump,
  zerocopy::{round_to_word, ZeroCopy, U16},
  BoxGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::{size_of, transmute},
  ops::Deref,
};
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[derive(Debug, Eq, PartialEq)]
pub struct CiphertextMetadata {
  fingerprint:      Sha3Hash,
  pub(crate) inner: CiphertextMetadataInner,
}

/// Metadata necessary for decryption (e.g., ephemeral keys, MACs, etc...)
#[derive(Eq, PartialEq)]
pub(crate) enum CiphertextMetadataInner {
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
}

impl Debug for CiphertextMetadataInner {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match self {
      CiphertextMetadataInner::Aes256Ctr { iv, mac } => {
        let mut df = f.debug_struct("Aes256Metadata");
        df.field("iv", iv);
        df.field("mac", mac);
        df.finish()
      },
      CiphertextMetadataInner::X25519Aes256Ctr { eph_pk, mac } => {
        let mut df = f.debug_struct("X25519Metadata");
        df.field("eph_pk", &ShortHexDump(&eph_pk[..], 32));
        df.field("mac", mac);
        df.finish()
      },
    }
  }
}

impl CiphertextMetadata {
  pub fn new_aes_256(fingerprint: Sha3Hash, iv: AesIv, mac: AesMac) -> Self {
    Self {
      fingerprint,
      inner: CiphertextMetadataInner::Aes256Ctr { iv, mac },
    }
  }

  pub fn get_aes_256(&self) -> Result<(&AesIv, &AesMac), GlyphErr> {
    match &self.inner {
      CiphertextMetadataInner::Aes256Ctr { iv, mac } => Ok((iv, mac)),
      _ => Err(err!(debug, GlyphErr::WrongCryptoScheme)),
    }
  }

  pub fn new_x25519(
    fingerprint: Sha3Hash,
    eph_pk: [u8; X25519_KEY_LEN],
    mac: AesMac,
  ) -> Self {
    Self {
      fingerprint,
      inner: CiphertextMetadataInner::X25519Aes256Ctr { eph_pk, mac },
    }
  }

  pub fn glyph_len(scheme: EncryptionSchemes) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<CiphertextMetadataHeader>()
      + size_of::<Sha3Hash>()
      + match scheme {
        EncryptionSchemes::Unknown => 0,
        EncryptionSchemes::Aes256Ctr => {
          size_of::<AesIv>() + size_of::<AesMac>()
        },
        EncryptionSchemes::X25519Aes256Ctr => {
          X25519_KEY_LEN + size_of::<AesMac>()
        },
      }
  }
}

impl CiphertextMetadataInner {
  fn encryption_scheme(&self) -> EncryptionSchemes {
    match self {
      CiphertextMetadataInner::Aes256Ctr { .. } => EncryptionSchemes::Aes256Ctr,
      CiphertextMetadataInner::X25519Aes256Ctr { .. } => {
        EncryptionSchemes::X25519Aes256Ctr
      },
    }
  }
}

impl ToGlyph for CiphertextMetadata {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();

    CiphertextMetadataHeader::new(self.inner.encryption_scheme())
      .bbwr(target, cursor)?;
    self.fingerprint.bbwr(target, cursor)?;
    match &self.inner {
      CiphertextMetadataInner::Aes256Ctr { iv, mac } => {
        iv.bbwr(target, cursor)?;
        mac.bbwr(target, cursor)?;
      },
      CiphertextMetadataInner::X25519Aes256Ctr { eph_pk, mac } => {
        u8::bbwrs(&eph_pk[..], target, cursor)?;
        mac.bbwr(target, cursor)?;
      },
    }
    glyph_close(GlyphType::CiphertextMetadata, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    match self.inner {
      CiphertextMetadataInner::Aes256Ctr { .. } => {
        CiphertextMetadata::glyph_len(EncryptionSchemes::Aes256Ctr)
      },
      CiphertextMetadataInner::X25519Aes256Ctr { .. } => {
        CiphertextMetadata::glyph_len(EncryptionSchemes::X25519Aes256Ctr)
      },
    }
  }
}

impl<B> FromGlyph<B> for CiphertextMetadata
where
  B: Glyph,
{
  fn from_glyph(source: B) -> Result<Self, GlyphErr> {
    let source = source.content_padded();
    let cursor = &mut 0;
    let ctm_header = CiphertextMetadataHeader::bbrf(source, cursor)?;
    let fingerprint = Sha3Hash::bbrd(source, cursor)?;
    match ctm_header.scheme() {
      EncryptionSchemes::Aes256Ctr => {
        let iv = AesIv::bbrd(source, cursor)?;
        let mac = AesMac::bbrd(source, cursor)?;
        Ok(CiphertextMetadata {
          fingerprint,
          inner: CiphertextMetadataInner::Aes256Ctr { iv, mac },
        })
      },
      EncryptionSchemes::X25519Aes256Ctr => {
        let eph_pk: [u8; 32] = u8::bbrda(source, cursor)?;
        let mac = AesMac::bbrd(source, cursor)?;
        Ok(CiphertextMetadata {
          fingerprint,
          inner: CiphertextMetadataInner::X25519Aes256Ctr { eph_pk, mac },
        })
      },
      _ => Err(err!(debug, GlyphErr::IllegalValue)),
    }
  }
}

/// Header used in encoding a `CiphertextMetadata`
#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(packed)]
pub struct CiphertextMetadataHeader {
  version:    u8,
  reserved_0: u8,
  scheme:     U16,
  reserved_1: [u8; 4],
}

unsafe impl ZeroCopy for CiphertextMetadataHeader {}

impl CiphertextMetadataHeader {
  pub fn new(scheme: EncryptionSchemes) -> Self {
    Self {
      version:    0,
      reserved_0: 0,
      scheme:     U16::from(scheme as u16),
      reserved_1: [0u8; 4],
    }
  }

  pub fn scheme(&self) -> EncryptionSchemes {
    let val = u16::from(self.scheme);
    val.into()
  }
}

/// A list of type IDs corresponding to the variants of [`CiphertextMetadata`].
//
// Updating?  Also update the unsafe transmute below.
#[repr(u16)]
pub enum EncryptionSchemes {
  Unknown = 0x0000,
  Aes256Ctr = 0x0001,
  X25519Aes256Ctr = 0x0002,
}

impl From<u16> for EncryptionSchemes {
  fn from(src: u16) -> Self {
    if src > EncryptionSchemes::X25519Aes256Ctr as u16 {
      EncryptionSchemes::Unknown
    } else {
      // SAFETY: Enum with checked contiguous values.
      unsafe { transmute::<u16, EncryptionSchemes>(src) }
    }
  }
}

/// A type used to create a glyph containing an encrypted glyph.
pub struct GlyphCrypter<G, K, KT>
where
  G: ToGlyph,
  K: Deref<Target = KT>,
  KT: EncryptionKey + ?Sized,
{
  glyph:    G,
  key:      K,
  rng_seed: [u8; 32],
}

impl<G, K, KT> GlyphCrypter<G, K, KT>
where
  G: ToGlyph,
  K: Deref<Target = KT>,
  KT: EncryptionKey + ?Sized,
{
  pub fn new<R>(glyph: G, key: K, mut rng: R) -> Self
  where
    R: RngCore + CryptoRng,
  {
    let mut rng_seed = [0u8; 32];
    rng.fill_bytes(&mut rng_seed[..]);
    GlyphCrypter {
      glyph,
      key,
      rng_seed,
    }
  }
}

impl<G, K, KT> ToGlyph for GlyphCrypter<G, K, KT>
where
  G: ToGlyph,
  K: Deref<Target = KT>,
  KT: EncryptionKey + ?Sized,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // Save room for headers and metadata
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    let mut metadata_cursor = *cursor;
    *cursor += self.key.metadata_glyph_len();

    // Encode the glyph as plaintext
    let crypt_start = *cursor;
    self.glyph.glyph_encode(target, cursor)?;
    let plaintext = &mut target[crypt_start..*cursor];

    //
    let rng = ChaCha20Rng::from_seed(self.rng_seed);
    let (_pt_hash, metadata) = self.key.encrypt(rng, plaintext)?;

    // Write the metadata and glyph headers
    metadata.glyph_encode(target, &mut metadata_cursor)?;
    glyph_close(GlyphType::EncryptedGlyph, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + self.key.metadata_glyph_len()
      + self.glyph.glyph_len()
  }
}

/// A glyph containing an encrypted glyph.
#[derive(Debug)]
pub struct EncryptedGlyph<T>
where
  T: Glyph,
{
  glyph:             T,
  metadata:          CiphertextMetadata,
  ciphertext_offset: usize,
}

impl<T> EncryptedGlyph<T>
where
  T: Glyph,
{
  #[cfg(feature = "alloc")]
  pub fn decrypt<K: DecryptionKey + ?Sized>(
    &self,
    key: &K,
  ) -> Result<(GlyphHash, BoxGlyph), GlyphErr> {
    let source = self.glyph.content();
    let cursor = &mut 0;

    // Grab ciphertext metadata
    let md_glyph = glyph_read(source, cursor)?;
    let metadata = CiphertextMetadata::from_glyph(md_glyph)?;

    // Copy ciphertext to a new memory buffer
    let ciphertext = &source[*cursor..];
    let mut buffer = BoxGlyph::new_buffer(ciphertext.len())?;
    buffer.as_mut().copy_from_slice(ciphertext);

    // Decrypt and interpret as a glyph.
    let hash = key.decrypt(&metadata, buffer.as_mut())?;
    let glyph = BoxGlyph::try_from(buffer)?;
    Ok((hash, glyph))
  }

  pub fn ciphertext_metadata(&self) -> &CiphertextMetadata {
    &self.metadata
  }

  pub fn ciphertext(&self) -> &[u8] {
    let content = self.glyph.content();
    if self.ciphertext_offset < content.len() {
      &content[self.ciphertext_offset..]
    } else {
      &[]
    }
  }
}

impl<T> FromGlyph<T> for EncryptedGlyph<T>
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::EncryptedGlyph)?;
    let source = glyph.content();
    let cursor = &mut 0;
    let metadata = glyph_read(source, cursor)?;
    let metadata = CiphertextMetadata::from_glyph(metadata)?;
    Ok(Self {
      glyph,
      metadata,
      ciphertext_offset: *cursor,
    })
  }
}

/// A builder used to create an encrypted extent glyph.
pub struct ExtentCrypter<E, DK, K>
where
  E: AsRef<[u8]>,
  DK: Deref<Target = K>,
  K: EncryptionKey + ?Sized,
{
  extent:   E,
  key:      DK,
  rng_seed: [u8; 32],
}

impl<E, DK, K> ExtentCrypter<E, DK, K>
where
  E: AsRef<[u8]>,
  DK: Deref<Target = K>,
  K: EncryptionKey + ?Sized,
{
  pub fn new<R>(extent: E, key: DK, mut rng: R) -> Self
  where
    R: RngCore + CryptoRng,
  {
    let mut rng_seed = [0u8; 32];
    rng.fill_bytes(&mut rng_seed[..]);
    ExtentCrypter {
      extent,
      key,
      rng_seed,
    }
  }
}

impl<E, DK, K> ToGlyph for ExtentCrypter<E, DK, K>
where
  E: AsRef<[u8]>,
  DK: Deref<Target = K>,
  K: EncryptionKey + ?Sized,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    // Save room for headers and metadata
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    let mut metadata_cursor = *cursor;
    *cursor += self.key.metadata_glyph_len();

    // Encode the extent as plaintext
    let crypt_start = *cursor;
    u8::bbwrs(self.extent.as_ref(), target, cursor)?;
    let plaintext = &mut target[crypt_start..*cursor];

    // Encrypt the plaintext
    let rng = ChaCha20Rng::from_seed(self.rng_seed);
    let (_pt_hash, metadata) = self.key.encrypt(rng, plaintext)?;

    // Write the metadata and glyph headers
    metadata.glyph_encode(target, &mut metadata_cursor)?;
    glyph_close(GlyphType::EncryptedExtent, target, offset, cursor, true)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + self.key.metadata_glyph_len()
      + round_to_word(self.extent.as_ref().len())
  }
}

/// A glyph containing unstructured encrypted data.
#[derive(Debug)]
pub struct EncryptedExtent<T>
where
  T: Glyph,
{
  glyph:             T,
  metadata:          CiphertextMetadata,
  ciphertext_offset: usize,
}

impl<T> EncryptedExtent<T>
where
  T: Glyph,
{
  #[cfg(feature = "alloc")]
  pub fn decrypt<K: DecryptionKey>(
    &self,
    key: &K,
  ) -> Result<(GlyphHash, alloc::boxed::Box<[u8]>), GlyphErr> {
    let mut buffer = alloc::boxed::Box::<[u8]>::try_from(self.ciphertext())?;

    let hash = key.decrypt(&self.metadata, buffer.as_mut())?;
    Ok((hash, buffer))
  }

  pub fn ciphertext_metadata(&self) -> &CiphertextMetadata {
    &self.metadata
  }

  pub fn ciphertext(&self) -> &[u8] {
    &self.glyph.content()[self.ciphertext_offset..]
  }
}

impl<T> FromGlyph<T> for EncryptedExtent<T>
where
  T: Glyph,
{
  fn from_glyph(glyph: T) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::EncryptedExtent)?;
    let source = glyph.content();
    let cursor = &mut 0;
    let metadata = glyph_read(source, cursor)?;
    let metadata = CiphertextMetadata::from_glyph(metadata)?;
    Ok(Self {
      glyph,
      metadata,
      ciphertext_offset: *cursor,
    })
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    crypto::{AesKey, TEST_PLAINTEXT},
    glyph::glyph_new,
    util::init_test_logger,
  };
  use rand::rngs::OsRng;

  #[test]
  fn codec_encrypted_glyph() {
    init_test_logger();

    // Set up RNG and key
    let mut rng = OsRng::default();
    let key = AesKey::new(&mut rng);

    // Encode with the `GlyphCrypter`
    let gc = GlyphCrypter::new("Hello, World", &key, &mut rng);
    let crypted_glyph = glyph_new(&gc).unwrap();

    // Result should decode as `EncryptedGlyph`
    let crypted_glyph = EncryptedGlyph::from_glyph(crypted_glyph).unwrap();

    // This is what it should decode as.
    let (_hash, decrypted_glyph) = crypted_glyph.decrypt(&key).unwrap();
    let msg = <&str>::from_glyph(decrypted_glyph.borrow()).unwrap();
    assert_eq!(msg, "Hello, World");
  }

  #[test]
  fn codec_encrypted_extent() {
    init_test_logger();

    // Set up RNG and key
    let mut rng = OsRng::default();
    let key = AesKey::new(&mut rng);

    // Encode with the `ExtentCrypter`.
    let gc = ExtentCrypter::new(TEST_PLAINTEXT, &key, &mut rng);
    let glyph = glyph_new(&gc).unwrap();

    let ee = EncryptedExtent::from_glyph(glyph).unwrap();

    let (_hash, decrypted_buf) = ee.decrypt(&key).unwrap();
    assert_eq!(decrypted_buf.as_ref(), TEST_PLAINTEXT);
  }
}
