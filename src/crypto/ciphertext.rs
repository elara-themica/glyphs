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
  BoxGlyph, BoxGlyphBuf,
};
use core::{
  fmt::{Debug, Formatter},
  mem::{size_of, transmute},
  ops::Deref,
};
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// Represents metadata associated with ciphertext necessary for decryption.
///
/// `CiphertextMetadata` encapsulates key information required for decrypting
/// encrypted data, such as key fingerprints, initialization vectors (IVs),
/// message authentication codes (MACs), and ephemeral public keys for certain
/// encryption schemes.
///
/// Currently, it supports two major encryption schemes:
/// - `Aes256Ctr`: Supporting CTR mode of AES-256 key, requiring an IV and MAC.
/// - `X25519_Aes256Ctr`: Combines X25519 elliptic-curve Diffie-Hellman (ECDH)
///   for key exchange with AES-256 for encryption and a MAC for message
///   authentication.
#[derive(Debug, Eq, PartialEq)]
pub struct CiphertextMetadata {
  fingerprint:      Sha3Hash,
  pub(super) inner: CiphertextMetadataInner,
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
  /// Creates a new `CiphertextMetadata` instance using AES-256-CTR encryption.
  ///
  /// # Parameters
  ///
  /// - `fingerprint`: A `Sha3Hash` that acts as a unique identifier or
  ///   fingerprint for the key.
  /// - `iv`: The initialization vector (`AesIv`) used for AES-256-CTR
  ///   encryption.  Note that, to avoid certain kinds of cryptanalysis, this
  ///   must be based on a nonce for this key (+ the # of bytes encrypted) that
  ///   does not overlap with other uses of this key.  If this cannot be
  ///   guaranteed, consider using a different form of encryption
  /// - `mac`: The message authentication code (`AesMac`) for verifying the
  ///   integrity and authenticity of the ciphertext.
  ///
  /// # Returns
  ///
  /// A new `CiphertextMetadata` instance with the provided fingerprint, IV, and MAC set for the AES-256-CTR scheme.
  pub fn new_aes_256(fingerprint: Sha3Hash, iv: AesIv, mac: AesMac) -> Self {
    Self {
      fingerprint,
      inner: CiphertextMetadataInner::Aes256Ctr { iv, mac },
    }
  }

  /// Retrieves the IV and MAC values associated with the AES-256-CTR encryption
  /// scheme.
  ///
  /// # Returns
  /// - `Ok((&AesIv, &AesMac))`: The initialization vector (IV) and message
  ///   authentication code (MAC) if the metadata corresponds to the
  ///   AES-256-CTR scheme.
  /// - `Err(GlyphErr)`: An error if the metadata does not correspond to the
  ///   AES-256-CTR encryption scheme.
  ///
  /// # Errors
  ///
  /// Returns `GlyphErr::WrongCryptoScheme` if the `CiphertextMetadata` instance
  /// uses a different encryption scheme.
  pub fn get_aes_256(&self) -> Result<(&AesIv, &AesMac), GlyphErr> {
    match &self.inner {
      CiphertextMetadataInner::Aes256Ctr { iv, mac } => Ok((iv, mac)),
      _ => Err(err!(debug, GlyphErr::WrongCryptoScheme)),
    }
  }

  /// Creates a new `CiphertextMetadata` instance using X25519 encryption
  /// combined with AES-256-CTR for authenticated encryption.
  ///
  /// # Parameters
  ///
  /// - `fingerprint`: A `Sha3Hash` that uniquely identifies the key.
  /// - `eph_pk`: The ephemeral public key (`[u8; X25519_KEY_LEN]`) used for the
  ///   Diffie-Hellman key agreement in the X25519 scheme.
  /// - `mac`: The message authentication code (`AesMac`) for verifying the
  ///   integrity and authenticity of the ciphertext.
  ///
  /// # Returns
  ///
  /// A new `CiphertextMetadata` instance with the provided fingerprint, ephemeral
  /// public key, and MAC set for the X25519 + AES-256-CTR encryption scheme.
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

  /// Calculates the total length of encryption metadata (a.k.a. "glyph")
  /// for a given encryption scheme.
  ///
  /// # Parameters
  ///
  /// - `scheme`: The encryption scheme ([`EncryptionSchemes`]) for which the
  ///   metadata size is computed. This determines the additional fields required
  ///   in the metadata.
  ///
  /// # Returns
  ///
  /// The total size of the encryption metadata (`usize`), including
  /// fixed-size headers and scheme-specific fields such as IVs, MACs, or keys.
  // TODO: Is this necessary?  Do we need the size before we have an instance?
  //       Document this here either way.
  pub(crate) fn glyph_len(scheme: EncryptionSchemes) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<CiphertextMetadataHeader>()
      + size_of::<Sha3Hash>()
      + match scheme {
        EncryptionSchemes::Unspecified => 0,
        EncryptionSchemes::Aes256Ctr => {
          size_of::<AesIv>() + size_of::<AesMac>()
        },
        EncryptionSchemes::X25519Aes256Ctr => {
          X25519_KEY_LEN + size_of::<AesMac>()
        },
        EncryptionSchemes::Unsupported => 0,
      }
  }
}

impl CiphertextMetadataInner {
  /// Returns the type of encryption scheme for which we have metadata.
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

/// Header used in encoding a [`CiphertextMetadata`]
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
  /// Creates a new header for an encoded [`CiphertextMetadata`].
  pub fn new(scheme: EncryptionSchemes) -> Self {
    Self {
      version:    0,
      reserved_0: 0,
      scheme:     U16::from(scheme as u16),
      reserved_1: [0u8; 4],
    }
  }

  /// Returns the type of encryption scheme used.
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
  /// The encryption scheme is deliberately unspecified
  Unspecified = 0x0000,
  /// AES-256 CTR Mode
  Aes256Ctr = 0x0001,
  /// X25519 Diffie-Hellman and AES-256 CTR Mode
  X25519Aes256Ctr = 0x0002,
  /// The encryption scheme is unsupported.
  Unsupported = 0x0003,
}

impl From<u16> for EncryptionSchemes {
  fn from(src: u16) -> Self {
    if src > EncryptionSchemes::Unsupported as u16 {
      EncryptionSchemes::Unsupported
    } else {
      // SAFETY: Enum with checked contiguous values.
      unsafe { transmute::<u16, EncryptionSchemes>(src) }
    }
  }
}

impl From<U16> for EncryptionSchemes {
  fn from(src: U16) -> Self {
    src.get().into()
  }
}

impl From<EncryptionSchemes> for u16 {
  fn from(value: EncryptionSchemes) -> Self {
    value as u16
  }
}

impl From<EncryptionSchemes> for U16 {
  fn from(value: EncryptionSchemes) -> Self {
    U16::from(value as u16)
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
  /// Creates a new `GlyphCrypter` instance with the given glyph, key, and
  /// random number generator.
  ///
  /// This function initializes an encryption context for the given glyph using
  /// the specified encryption key. A random seed is generated from the provided
  /// RNG to ensure unique encryption for each instance.
  ///
  /// # Parameters
  /// - `glyph`: The glyph to be encrypted.
  /// - `key`: A reference to the encryption key used for encrypting the glyph.
  /// - `rng`: A cryptographically secure random number generator to produce a
  ///   deterministic seed.
  ///
  /// # Returns
  /// A new `GlyphCrypter` instance ready for glyph encryption.
  ///
  /// # Type Parameters
  /// - `R`: A type implementing [`RngCore`] and [`CryptoRng`], used as the
  ///   random number generator.
  /// - `G`: A type implementing [`ToGlyph`], representing the glyph to be
  ///   encrypted.
  /// - `K`: A type that dereferences to `KT`.
  /// - `KT`: A type implementing [`EncryptionKey`], specifying the encryption
  ///   key behavior.
  // TODO: Can this be simplified?
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
  // TODO: Convert this into a GlyphOffset
  ciphertext_offset: usize,
}

impl<T> EncryptedGlyph<T>
where
  T: Glyph,
{
  /// Decrypts the encrypted glyph using the provided decryption key.
  ///
  /// This function interprets the internal representation of the encrypted glyph,
  /// extracts the metadata and ciphertext, and decrypts the contents using the
  /// given decryption key. Once decrypted, the plaintext is returned as a new
  /// `BoxGlyph` along with its associated hash.
  ///
  /// # Parameters
  /// - `key`: A reference to a decryption key implementing [`DecryptionKey`].
  ///
  /// # Returns
  /// A `Result` containing a tuple with the glyph hash and the decrypted `BoxGlyph`
  /// on success, or a `GlyphErr` on failure.
  ///
  /// # Errors
  /// Returns an error in case of:
  /// - Invalid metadata or ciphertext.
  /// - Failure during decryption.
  /// - Inability to interpret the decrypted contents as a glyph.
  #[cfg(feature = "alloc")]
  pub fn decrypt<K: DecryptionKey + ?Sized>(
    &self,
    key: &K,
  ) -> Result<BoxGlyph, GlyphErr> {
    let source = self.glyph.content();
    let cursor = &mut 0;

    // Grab ciphertext metadata
    let md_glyph = glyph_read(source, cursor)?;
    let metadata = CiphertextMetadata::from_glyph(md_glyph)?;

    // Copy ciphertext to a new memory buffer
    let ciphertext = &source[*cursor..];
    let mut buffer = BoxGlyphBuf::new(ciphertext.len())?;
    buffer.as_mut().copy_from_slice(ciphertext);

    // Decrypt and interpret as a glyph.
    let hash = key.decrypt(&metadata, buffer.as_mut())?;
    buffer.set_known_hash(&hash);
    buffer.finalize()
  }

  /// Retrieves a reference to the ciphertext metadata associated with this
  /// `EncryptedGlyph`.
  ///
  /// This metadata contains details necessary for decryption, such as
  /// encryption algorithms and key identifiers used during encryption.
  ///
  /// # Returns
  /// A zero-copy reference to the [`CiphertextMetadata`] contained within the
  /// encrypted glyph
  pub fn ciphertext_metadata(&self) -> &CiphertextMetadata {
    &self.metadata
  }

  /// Returns the ciphertext of the encrypted glyph as a byte slice.
  ///
  /// This function retrieves the internal ciphertext contained within
  /// the encrypted glyph.
  ///
  /// # Returns
  /// A byte slice representing the ciphertext.
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

/// Creates an encrypted extent when encoded as a glyph.
///
/// This type create an encrypted extent glyph.  It can be used either
/// immediately or as part of a larger structure, in which case the extent
/// is encrypted as part of the encoding process rather than requiring a
/// separate memory allocation and duplication.
pub struct ExtentCrypter<E, K>
where
  E: AsRef<[u8]>,
  K: EncryptionKey,
{
  extent:   E,
  key:      K,
  rng_seed: [u8; 32],
}

impl<E, K> ExtentCrypter<E, K>
where
  E: AsRef<[u8]>,
  K: EncryptionKey,
{
  /// Creates a new `ExtentCrypter`.
  ///
  /// # Parameters
  /// - `extent`: The unencrypted data to be encrypted.
  /// - `key`: The encryption key used to encrypt the data.
  /// - `rng`: A cryptographically secure random number generator used
  ///   for generating a random seed for encryption.
  pub fn new<R>(extent: E, key: K, mut rng: R) -> Self
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

impl<E, K> ToGlyph for ExtentCrypter<E, K>
where
  E: AsRef<[u8]>,
  K: EncryptionKey,
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
  // TODO: Convert to using a GlyphOffset
  ciphertext_offset: usize,
}

impl<T> EncryptedExtent<T>
where
  T: Glyph,
{
  /// Decrypts the ciphertext using the provided decryption key.
  ///
  /// # Parameters
  /// - `key`: The decryption key used to decrypt the ciphertext.
  ///
  /// # Returns
  /// If successful, returns a tuple consisting of:
  /// - `GlyphHash`: A hash of the decrypted glyph content.
  /// - `Box<[u8]>`: The decrypted data as a dynamically allocated byte buffer.
  ///
  /// # Errors
  /// Returns a `GlyphErr` if the decryption process fails, for example,
  /// due to an invalid key or corrupted ciphertext.
  // TODO: Make an encrypted extent buffer that includes the hash.
  #[cfg(feature = "alloc")]
  pub fn decrypt<K: DecryptionKey>(
    &self,
    key: K,
  ) -> Result<(GlyphHash, alloc::boxed::Box<[u8]>), GlyphErr> {
    let mut buffer = alloc::boxed::Box::<[u8]>::try_from(self.ciphertext())?;

    let hash = key.decrypt(&self.metadata, buffer.as_mut())?;
    Ok((hash, buffer))
  }

  /// Retrieves the ciphertext metadata associated with this encrypted extent.
  ///
  /// This metadata contains information necessary for decryption, such as
  /// encryption algorithm details or associated data.
  ///
  /// # Returns
  /// A zero-copy reference to the [`CiphertextMetadata`] associated with this
  /// encrypted extent.
  pub fn ciphertext_metadata(&self) -> &CiphertextMetadata {
    &self.metadata
  }

  /// Retrieves the ciphertext of the encrypted extent.
  ///
  /// The ciphertext represents the raw encrypted data stored within this
  /// instance. The data begins at the `ciphertext_offset` computed during
  /// construction and extends to the end of the glyph content.
  ///
  /// # Returns
  /// A byte slice (`&[u8]`) referencing the ciphertext within the glyph content.
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
    let decrypted_glyph = crypted_glyph.decrypt(&key).unwrap();
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
    let gc = ExtentCrypter::new(TEST_PLAINTEXT, key, &mut rng);
    let glyph = glyph_new(&gc).unwrap();

    let ee = EncryptedExtent::from_glyph(glyph).unwrap();

    let (_hash, decrypted_buf) = ee.decrypt(key).unwrap();
    assert_eq!(decrypted_buf.as_ref(), TEST_PLAINTEXT);
  }
}
