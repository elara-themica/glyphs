//! Types related storing encrypted passwords and encrypting data using a
//! password as a key.
use crate::{
  crypto::{
    aes_256ctr_decrypt, aes_256ctr_encrypt, AesIv, AesKey, CiphertextMetadata,
    CryptographicHash, DecryptionKey, EncryptionKey, EncryptionSchemes,
    GlyphHash, HashContext, Sha3Context, Sha3Hash,
  },
  glyph::{FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph},
  util::debug::ShortHexDump,
  zerocopy::{ZeroCopy, U16},
};
use argon2::{hash_raw, Config};
use core::{
  fmt::Debug,
  mem::{size_of, transmute},
};
use rand::{CryptoRng, RngCore};

/// A password to be used as an encryption and/or decryption key.
pub struct PasswordKey<T>
where
  T: AsRef<[u8]>,
{
  password: T,
}

impl<T> PasswordKey<T>
where
  T: AsRef<[u8]>,
{
  pub fn new(password: T) -> Result<Self, GlyphErr> {
    Ok(PasswordKey { password })
  }

  /// Generates an AES key from a password, salted by the IV.
  ///
  ///
  fn calculate_key(&self, iv: &AesIv) -> AesKey {
    let mut ctx = Sha3Context::new();
    ctx.update(iv.bytes());
    ctx.update(self.password.as_ref());
    let hash = ctx.finish();
    AesKey::from(*hash.hash_bytes())
  }
}

impl<T> Debug for PasswordKey<T>
where
  T: AsRef<[u8]>,
{
  fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
    write!(f, "PasswordKey(")?;
    let pw_string = core::str::from_utf8(self.password.as_ref());
    match pw_string {
      Ok(str) => write!(f, "UTF-8/\"{}\"", str)?,
      Err(_) => {
        write!(f, "Bytes/{:?}", ShortHexDump(self.password.as_ref(), 8))?
      },
    }
    write!(f, " }}")
  }
}

impl<T> EncryptionKey for PasswordKey<T>
where
  T: AsRef<[u8]>,
{
  fn metadata_glyph_len(&self) -> usize {
    CiphertextMetadata::glyph_len(EncryptionSchemes::Aes256Ctr)
  }

  fn encrypt<R: RngCore + CryptoRng>(
    &self,
    rng: R,
    data: &mut [u8],
  ) -> Result<(GlyphHash, CiphertextMetadata), GlyphErr> {
    let iv = AesIv::new(rng);
    let key = self.calculate_key(&iv);
    let key_hash = Sha3Hash::new(key.bytes());
    let (hash, mac) = aes_256ctr_encrypt(&key, &iv, data);
    Ok((hash, CiphertextMetadata::new_aes_256(key_hash, iv, mac)))
  }
}

impl<T> DecryptionKey for PasswordKey<T>
where
  T: AsRef<[u8]>,
{
  fn decrypt(
    &self,
    metadata: &CiphertextMetadata,
    data: &mut [u8],
  ) -> Result<GlyphHash, GlyphErr> {
    let (iv, mac) = metadata.get_aes_256()?;
    let key = self.calculate_key(iv);
    let pt_hash = aes_256ctr_decrypt(&key, &iv, &mac, data)?;
    Ok(pt_hash)
  }
}

/// A salted and hashed password (currently using the `argon2` crate)
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(C)]
pub struct EncryptedPassword {
  salt: [u8; 16],
  hash: [u8; 32],
}

/// SAFETY: Byte arrays are inherently zero copy
unsafe impl ZeroCopy for EncryptedPassword {}

impl EncryptedPassword {
  /// Creates a new hash for the provided password (with a random salt)
  ///
  /// Requires the `alloc` feature because the `argon2` crate's `hash_raw`
  /// function returns a `Vec<u8>`.
  #[cfg(feature = "alloc")]
  pub fn new<R>(password: &[u8], mut rng: R) -> Self
  where
    R: RngCore + CryptoRng,
  {
    let mut config = Config::default();
    config.hash_length = 32;

    let mut salt = [0u8; 16];
    rng.fill_bytes(&mut salt[..]);

    let hash_bytes = hash_raw(password, &salt[..], &config).unwrap();
    let mut hash = [0u8; 32];
    hash.clone_from_slice(&hash_bytes[..]);
    EncryptedPassword { salt, hash }
  }

  /// Returns `true` iff the provided password is correct
  pub fn matches(&self, password: &[u8]) -> bool {
    let mut config = Config::default();
    config.hash_length = 32;
    let calc_hash = hash_raw(password, &self.salt[..], &config).unwrap();
    calc_hash[..] == self.hash[..]
  }
}

impl ToGlyph for EncryptedPassword {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let glyph_header = GlyphHeader::new(
      GlyphType::EncryptedPassword,
      size_of::<EncryptedPasswordHeader>() + size_of::<Self>(),
    )?;
    let password_header =
      EncryptedPasswordHeader::new(EncryptedPasswordTypes::Argon2Default);
    glyph_header.bbwr(target, cursor)?;
    password_header.bbwr(target, cursor)?;
    self.bbwr(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<EncryptedPasswordHeader>()
      + size_of::<Self>()
  }
}

impl<T> FromGlyph<T> for EncryptedPassword
where
  T: Glyph,
{
  fn from_glyph(source: T) -> Result<Self, GlyphErr> {
    source.confirm_type(GlyphType::EncryptedPassword)?;
    let source = source.content_padded();
    let cursor = &mut 0;
    let eph = EncryptedPasswordHeader::bbrd(source, cursor)?;
    if eph.pw_type != U16::from(EncryptedPasswordTypes::Argon2Default) {
      return Err(err!(
        error,
        GlyphErr::UnexpectedSubType {
          type_index:       0,
          expected_type_id: EncryptedPasswordTypes::Argon2Default as u32,
          observed_type_id: u32::from(u16::from(eph.pw_type)),
        }
      ));
    }
    Ok(Self::bbrd(source, cursor)?)
  }
}

/// An internal header used for serializing encrypted passwords.
// This is mostly just here for later; going to leave it largely unspecified
// until there's more than one way to store encrypted passwords.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(C)]
struct EncryptedPasswordHeader {
  version:    u8,
  reserved_0: u8,
  pw_type:    U16,
  reserved_1: [u8; 4],
}

impl EncryptedPasswordHeader {
  pub fn new(pw_type: EncryptedPasswordTypes) -> Self {
    Self {
      version:    0,
      reserved_0: 0,
      pw_type:    pw_type.into(),
      reserved_1: Default::default(),
    }
  }
}

unsafe impl ZeroCopy for EncryptedPasswordHeader {}

/// A list of supported encrypted password types (currently `argon2` only)
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum EncryptedPasswordTypes {
  Unknown = 0x0000,
  Argon2Default = 0x0001,
}

impl EncryptedPasswordTypes {
  const HIGHEST_KNOWN_ID: u16 = Self::Argon2Default as u16;
}

impl From<u16> for EncryptedPasswordTypes {
  fn from(src: u16) -> Self {
    if src > Self::HIGHEST_KNOWN_ID {
      Self::Unknown
    } else {
      unsafe { transmute::<u16, Self>(src) }
    }
  }
}

impl From<EncryptedPasswordTypes> for u16 {
  fn from(src: EncryptedPasswordTypes) -> Self {
    src as u16
  }
}

impl From<EncryptedPasswordTypes> for U16 {
  fn from(src: EncryptedPasswordTypes) -> Self {
    U16::from(src as u16)
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{crypto::TEST_PLAINTEXT, glyph_new, util::init_test_logger};
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[test]
  fn crypto_password_key() -> Result<(), GlyphErr> {
    init_test_logger();

    let mut rng = ChaCha20Rng::from_seed([32; 32]);
    let key = PasswordKey::new(b"hunter2")?;

    let mut message: alloc::boxed::Box<[u8]> =
      alloc::boxed::Box::try_from(&TEST_PLAINTEXT[..])?;
    dbg!(ShortHexDump(message.as_ref(), 8));

    let (_ct_hash, md) = key.encrypt(&mut rng, message.as_mut())?;
    dbg!(ShortHexDump(message.as_ref(), 8));

    key.decrypt(&md, message.as_mut())?;
    dbg!(ShortHexDump(message.as_ref(), 8));

    assert_eq!(message.as_ref(), &TEST_PLAINTEXT[..]);

    Ok(())
  }

  #[test]
  fn codec_password() -> Result<(), GlyphErr> {
    init_test_logger();

    let mut rng = ChaCha20Rng::from_seed([32; 32]);
    let p = EncryptedPassword::new(b"hunter2", &mut rng);
    assert!(p.matches(b"hunter2"));
    assert!(!p.matches(b"password"));

    let pg = glyph_new(&p)?;
    dbg!(&pg);
    let decoded = EncryptedPassword::from_glyph(pg.borrow())?;
    assert_eq!(decoded, p);

    Ok(())
  }
}
