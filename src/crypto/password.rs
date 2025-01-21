//! Types related storing encrypted passwords and encrypting data using a
//! password as a key.
use crate::{
  crypto::{
    aes_256ctr_decrypt, aes_256ctr_encrypt, AesIv, AesKey, CiphertextMetadata,
    CryptographicHash, DecryptionKey, EncryptionKey, EncryptionSchemes,
    GlyphHash, HashContext, Sha3Context, Sha3Hash,
  },
  glyph::{
    glyph_close, FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph,
  },
  util::debug::ShortHexDump,
  zerocopy::{round_to_word, ZeroCopy, U16},
  EncodedGlyph, FromGlyphErr, GlyphSorting, ParsedGlyph,
};
use argon2::{Algorithm, Version};
use core::{
  fmt::{Debug, Formatter},
  mem::{size_of, transmute},
  slice::from_raw_parts,
};
use rand::{CryptoRng, Rng, RngCore};
use std::cmp::Ordering;

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
#[allow(non_camel_case_types)]
pub enum Password {
  /// Password encrypted with the Argon2id algorithm.
  ///
  /// A password hashed using the Argon2id variant of the Argon2 algorithm,
  /// version 19, with a 16-byte salt and a 32-byte digest.
  Argon2id_v19_s16_d32 {
    salt:   [u8; 16],
    digest: [u8; 32],
    /// Memory cost, in units of 1024 bytes.
    m_cost: u8,
    /// Parallelism cost
    p_cost: u8,
    /// Time cost (iterations)
    t_cost: u8,
  },
}

impl Password {
  /// Creates a new hash for the provided password (with a random salt)
  ///
  /// Requires the `alloc` feature because the `argon2` crate's `hash_raw`
  /// function returns a `Vec<u8>`.
  #[cfg(feature = "alloc")]
  pub fn new_default<R>(password: &[u8], mut rng: R) -> Result<Self, GlyphErr>
  where
    R: RngCore + CryptoRng,
  {
    Self::new_argon2id(password, &mut rng)
  }

  pub fn new_argon2id<R>(password: &[u8], mut rng: R) -> Result<Self, GlyphErr>
  where
    R: RngCore + CryptoRng,
  {
    let (m_cost, t_cost, p_cost) = (19, 2, 1);

    let params = argon2::Params::new(
      m_cost as u32,
      t_cost as u32,
      p_cost as u32,
      Some(32),
    )
    .map_err(|_| GlyphErr::Argon2Error)?;

    let hasher =
      argon2::Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
    let salt = rng.gen::<[u8; 16]>();
    let mut digest = [0u8; 32];
    let mut hasher_mem = [argon2::Block::new(); 20];
    hasher
      .hash_password_into_with_memory(
        password,
        &salt[..],
        &mut digest,
        &mut hasher_mem,
      )
      .map_err(|_| GlyphErr::Argon2Error)?;

    Ok(Self::Argon2id_v19_s16_d32 {
      salt,
      digest,
      m_cost,
      p_cost,
      t_cost,
    })
  }

  /// Returns `true` iff the provided password is correct
  pub fn matches(&self, password: &[u8]) -> Result<bool, GlyphErr> {
    match self {
      Password::Argon2id_v19_s16_d32 {
        salt,
        digest,
        m_cost,
        p_cost,
        t_cost,
      } => {
        let params = argon2::Params::new(
          *m_cost as u32,
          *t_cost as u32,
          *p_cost as u32,
          Some(32),
        )
        .map_err(|_| GlyphErr::Argon2Error)?;

        let hasher =
          argon2::Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
        let mut new_digest = [0u8; 32];
        let mut hasher_mem = [argon2::Block::new(); 20];
        hasher
          .hash_password_into_with_memory(
            password,
            &salt[..],
            &mut new_digest,
            &mut hasher_mem,
          )
          .map_err(|_| GlyphErr::Argon2Error)?;
        Ok(&new_digest[..] == &digest[..])
      },
    }
  }
}

impl ToGlyph for Password {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let glyph_offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    match self {
      Password::Argon2id_v19_s16_d32 {
        salt,
        digest,
        m_cost,
        p_cost,
        t_cost,
      } => {
        let params_header = Argon2idParametersHeader {
          version: 19,
          m_cost:  *m_cost,
          p_cost:  *p_cost,
          t_cost:  *t_cost,
        };
        let pass_header = PasswordGlyphHeader {
          algorithm_id: U16::from(PasswordAlgorithm::Argon2id_v19_s16_d32),
          salt_len:     16,
          digest_len:   32,
          algo_params:  params_header.into(),
        };
        pass_header.bbwr(target, cursor)?;
        u8::bbwrs(salt, target, cursor)?;
        u8::bbwrs(digest, target, cursor)?;
      },
    }
    glyph_close(
      GlyphType::EncryptedPassword,
      target,
      glyph_offset,
      cursor,
      true,
    )
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + round_to_word(
        size_of::<PasswordGlyphHeader>()
          + match self {
            Password::Argon2id_v19_s16_d32 { .. } => 16 + 32,
          },
      )
  }
}

/// An internal header used for serializing encrypted passwords.
// This is mostly just here for later; going to leave it largely unspecified
// until there's more than one way to store encrypted passwords.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
struct PasswordGlyphHeader {
  algorithm_id: U16,
  salt_len:     u8,
  digest_len:   u8,
  algo_params:  [u8; 4],
}

impl PasswordGlyphHeader {
  /// Creates a new `PasswordGlyphHeader` with the specified parameters.
  pub fn new(
    algorithm: PasswordAlgorithm,
    salt_len: usize,
    digest_len: usize,
    algo_params: impl Into<[u8; 4]>,
  ) -> Result<Self, GlyphErr> {
    let salt_len = u8::try_from(salt_len)
      .map_err(|_| GlyphErr::PasswordSaltLen(salt_len))?;
    let digest_len = u8::try_from(digest_len)
      .map_err(|_| GlyphErr::PasswordDigestLen(digest_len))?;
    let algo_params: [u8; 4] = algo_params.into();

    Ok(Self {
      algorithm_id: algorithm.into(),
      salt_len,
      digest_len,
      algo_params,
    })
  }

  /// Returns the algorithm identifier.
  pub fn algorithm(&self) -> PasswordAlgorithm {
    PasswordAlgorithm::from(self.algorithm_id.get())
  }

  /// Returns the salt length.
  pub fn salt_len(&self) -> usize {
    self.salt_len as usize
  }

  /// Returns the digest length.
  pub fn digest_len(&self) -> usize {
    self.digest_len as usize
  }

  /// Returns the algorithm parameters.
  pub fn algo_params(&self) -> [u8; 4] {
    self.algo_params
  }
}

unsafe impl ZeroCopy for PasswordGlyphHeader {}

/// Parameters for the Argon2id Password Algorithm
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
struct Argon2idParametersHeader {
  /// Version
  version: u8,
  /// Memory cost, in units of 1024 bytes.
  m_cost:  u8,
  /// Parallelism cost
  p_cost:  u8,
  /// Time cost (iterations)
  t_cost:  u8,
}

impl Into<[u8; 4]> for Argon2idParametersHeader {
  fn into(self) -> [u8; 4] {
    // SAFETY: Reprs are identical, all bit patterns valid.
    unsafe { transmute::<Self, [u8; 4]>(self) }
  }
}

impl Into<Argon2idParametersHeader> for [u8; 4] {
  fn into(self) -> Argon2idParametersHeader {
    // SAFETY: Reprs are identical, all bit patterns valid.
    unsafe { transmute::<[u8; 4], Argon2idParametersHeader>(self) }
  }
}

unsafe impl ZeroCopy for Argon2idParametersHeader {}

/// A list of supported encrypted password types (currently `argon2` only)
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[allow(non_camel_case_types)]
pub enum PasswordAlgorithm {
  Unknown = 0x0000,
  Argon2id_v19_s16_d32 = 0x0001,
  UnknownType = 0x0002,
  // SAFETY: IDs must be continuous, and `UnknownType` must always be the one
  // with the highest value.
}

impl PasswordAlgorithm {}

impl From<u16> for PasswordAlgorithm {
  fn from(src: u16) -> Self {
    if src > Self::UnknownType as u16 {
      Self::UnknownType
    } else {
      unsafe { transmute::<u16, Self>(src) }
    }
  }
}

impl From<U16> for PasswordAlgorithm {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<PasswordAlgorithm> for u16 {
  fn from(src: PasswordAlgorithm) -> Self {
    src as u16
  }
}

impl From<PasswordAlgorithm> for U16 {
  fn from(src: PasswordAlgorithm) -> Self {
    U16::from(src as u16)
  }
}

pub struct PasswordGlyph<G: Glyph> {
  glyph:  G,
  salt:   *const u8,
  digest: *const u8,
}

impl<G: Glyph> PasswordGlyph<G> {
  fn header(&self) -> &PasswordGlyphHeader {
    let content = self.glyph.content_padded();
    // SAFETY: `from_glyph()` guarantees that contents contains a valid header.
    unsafe { PasswordGlyphHeader::bbrf_u(content, &mut 0) }
  }

  /// Returns the algorithm used to encrypt the password.
  pub fn algorithm(&self) -> PasswordAlgorithm {
    self.header().algorithm()
  }

  /// Returns the salt used before calculating the password digest.
  pub fn salt(&self) -> &[u8] {
    let header = self.header();
    let salt_len = header.salt_len();
    unsafe { from_raw_parts(self.salt, salt_len) }
  }

  /// Returns the digest of the salted password
  pub fn digest(&self) -> &[u8] {
    let header = self.header();
    let digest_len = header.digest_len();
    unsafe { from_raw_parts(self.digest, digest_len) }
  }

  /// Decodes the `Password` stored in this glyph.
  pub fn password(&self) -> Result<Password, GlyphErr> {
    match self.header().algorithm() {
      PasswordAlgorithm::Argon2id_v19_s16_d32 => {
        let algo_params: Argon2idParametersHeader =
          self.header().algo_params().into();
        let (salt, digest) = unsafe {
          (
            transmute::<*const u8, &[u8; 16]>(self.salt),
            transmute::<*const u8, &[u8; 32]>(self.digest),
          )
        };
        let pw = Password::Argon2id_v19_s16_d32 {
          salt:   *salt,
          digest: *digest,
          m_cost: algo_params.m_cost,
          p_cost: algo_params.p_cost,
          t_cost: algo_params.t_cost,
        };
        Ok(pw)
      },
      _ => Err(GlyphErr::PasswordUnknownAlgorithm(
        self.header().algorithm_id.get(),
      )),
    }
  }

  /// Returns `true` if the provided password matches.
  pub fn matches(&self, password: &[u8]) -> Result<bool, GlyphErr> {
    let pw = self.password()?;
    pw.matches(password)
  }
}

impl<G: Glyph> FromGlyph<G> for PasswordGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    /*  SAFETY:  We guarantee the following:

       - The glyph contains a full `PasswordGlyphHeader`.
       - The glyph is of sufficient length to contain the salt and digest as
         specified in that header, and their associated pointers are valid.
       - If the password type is known, the salt and digest lengths match
         what is expected by those password algorithms.
    */
    if let Err(err) = glyph.confirm_type(GlyphType::EncryptedPassword) {
      return Err(err.into_fge(glyph));
    }
    let content = glyph.content();
    let mut cursor = 0;
    let pw_header = match PasswordGlyphHeader::bbrd(content, &mut cursor) {
      Ok(pw_header) => pw_header,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    let salt_len = pw_header.salt_len();
    let digest_len = pw_header.digest_len();
    let salt = match u8::bbrfs(content, &mut cursor, salt_len) {
      Ok(salt) => salt,
      Err(err) => return Err(err.into_fge(glyph)),
    };
    let digest = match u8::bbrfs(content, &mut cursor, digest_len) {
      Ok(digest) => digest,
      Err(err) => return Err(err.into_fge(glyph)),
    };

    match pw_header.algorithm() {
      PasswordAlgorithm::Argon2id_v19_s16_d32 => {
        if salt.len() != 16 || digest.len() != 32 {
          return Err(
            GlyphErr::PasswordInvalidByteLen {
              algorithm:       pw_header.algorithm_id.get(),
              salt_expected:   16,
              salt_actual:     salt.len(),
              digest_expected: 32,
              digest_actual:   digest.len(),
            }
            .into_fge(glyph),
          );
        }
      },
      _ => {}, // Nothing; salt and digest lengths need to be taken from header.
    }

    let salt = salt.as_ptr();
    let digest = digest.as_ptr();

    Ok(Self {
      glyph,
      salt,
      digest,
    })
  }
}

impl<G: Glyph> Debug for PasswordGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("PasswordGlyph");
    df.field("salt", &ShortHexDump(self.salt(), 0));
    df.field("digest", &ShortHexDump(self.digest(), 0));
    df.field("algorithm", &self.algorithm());
    match self.algorithm() {
      PasswordAlgorithm::Argon2id_v19_s16_d32 => {
        let params: Argon2idParametersHeader =
          self.header().algo_params().into();
        df.field("m_cost", &params.m_cost);
        df.field("p_cost", &params.p_cost);
        df.field("t_cost", &params.t_cost);
      },
      _ => {},
    }
    df.finish()
  }
}

impl<G: Glyph> PartialEq for PasswordGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Glyph> Eq for PasswordGlyph<G> {}

impl<G: Glyph> PartialOrd for PasswordGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Glyph> Ord for PasswordGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, GlyphSorting::default())
  }
}

impl<G: Glyph> EncodedGlyph<G> for PasswordGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> ParsedGlyph<'_> {
    self.glyph.borrow()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::ByteOrder => {
        let a = self.glyph.borrow();
        let b = other.glyph.borrow();
        a.glyph_type()
          .cmp(&b.glyph_type())
          .then_with(|| a.content().cmp(b.content()))
      },
      GlyphSorting::Experimental => self
        .header()
        .algorithm_id
        .get()
        .cmp(&other.header().algorithm_id.get())
        .then_with(|| self.salt().cmp(other.salt()))
        .then_with(|| self.digest().cmp(other.digest())),
    }
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
  fn passwords() {
    init_test_logger();

    //== Correct function of `Password` ==//
    let pw1 = b"hunter2";
    let pw2 = b"correcthorsebatterystaple";

    let mut rng = ChaCha20Rng::from_seed([32; 32]);
    let epw1 = Password::new_argon2id(pw1, &mut rng).unwrap();
    let epw2 = Password::new_argon2id(pw2, &mut rng).unwrap();

    assert!(epw1.matches(pw1).unwrap());
    assert!(!epw1.matches(pw2).unwrap());
    assert!(epw2.matches(pw2).unwrap());
    assert!(!epw2.matches(pw1).unwrap());

    //== Round Trip Codec of `Password` into `PasswordGlyph` ==//
    let g = glyph_new(&epw1).unwrap();
    std::dbg!(&g);
    let pwg = PasswordGlyph::from_glyph(g).unwrap();
    dbg!(&pwg);
    let epw1_2 = pwg.password().unwrap();
    assert_eq!(epw1, epw1_2);

    //== Operation of password checking directly from `PasswordGlyph` ==//
    assert!(pwg.matches(pw1).unwrap());
    assert!(!pwg.matches(pw2).unwrap());
  }

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
}
