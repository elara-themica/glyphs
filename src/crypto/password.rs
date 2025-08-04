//! Types related storing encrypted passwords and encrypting data using a
//! password as a key.
use crate::{
  glyph::{FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph},
  util::{debug::ShortHexDump, LogErr},
  zerocopy::{
    bounds_check, pad_to_word, round_to_word, BufferErr, ZeroCopy, U16, U32,
  },
  DecodeErr, EncodedGlyph, GlyphSorting,
};
use argon2::{Algorithm, Version};
use core::{
  cmp::Ordering,
  fmt::{Debug, Formatter},
  mem::{size_of, transmute},
  ops::Deref,
};
use log::Level;
use pbkdf2::hmac::Hmac;
use smallvec::SmallVec;

// /// A password to be used as an encryption and/or decryption key.
// pub struct PasswordKey<T>
// where
//   T: AsRef<[u8]>,
// {
//   password: T,
// }
//
// impl<T> PasswordKey<T>
// where
//   T: AsRef<[u8]>,
// {
//   pub fn new(password: T) -> Result<Self, GlyphErr> {
//     Ok(PasswordKey { password })
//   }
//
//   /// Generates an AES key from a password, salted by the IV.
//   ///
//   ///
//   fn calculate_key(&self, iv: &AesIv) -> AesKey {
//     let mut ctx = Sha3Context::new();
//     ctx.update(iv.bytes());
//     ctx.update(self.password.as_ref());
//     let hash = ctx.finish();
//     AesKey::from(*hash.hash_bytes())
//   }
// }
//
// impl<T> Debug for PasswordKey<T>
// where
//   T: AsRef<[u8]>,
// {
//   fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
//     write!(f, "PasswordKey(")?;
//     let pw_string = core::str::from_utf8(self.password.as_ref());
//     match pw_string {
//       Ok(str) => write!(f, "UTF-8/\"{}\"", str)?,
//       Err(_) => {
//         write!(f, "Bytes/{:?}", ShortHexDump(self.password.as_ref(), 8))?
//       },
//     }
//     write!(f, " }}")
//   }
// }
//
// impl<T> EncryptionKey for PasswordKey<T>
// where
//   T: AsRef<[u8]>,
// {
//   fn metadata_glyph_len(&self) -> usize {
//     CiphertextMetadata::glyph_len(EncryptionSchemes::Aes256Ctr)
//   }
//
//   fn encrypt<R: RngCore + CryptoRng>(
//     &self,
//     rng: R,
//     data: &mut [u8],
//   ) -> Result<(GlyphHash, CiphertextMetadata), GlyphErr> {
//     let iv = AesIv::new(rng);
//     let key = self.calculate_key(&iv);
//     let key_hash = Sha3Hash::new(key.bytes());
//     let (hash, mac) = aes_256ctr_encrypt(&key, &iv, data);
//     Ok((hash, CiphertextMetadata::new_aes_256(key_hash, iv, mac)))
//   }
// }
//
// impl<T> DecryptionKey for PasswordKey<T>
// where
//   T: AsRef<[u8]>,
// {
//   fn decrypt(
//     &self,
//     metadata: &CiphertextMetadata,
//     data: &mut [u8],
//   ) -> Result<GlyphHash, GlyphErr> {
//     let (iv, mac) = metadata.get_aes_256()?;
//     let key = self.calculate_key(iv);
//     let pt_hash = aes_256ctr_decrypt(&key, &iv, &mac, data)?;
//     Ok(pt_hash)
//   }
// }

/// A salted and hashed password (currently using the `argon2` crate)
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(C)]
pub struct Password {
  salt:   SmallVec<u8, 16>,
  digest: SmallVec<u8, 32>,
  inner:  PasswordAlgorithmParameters,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
enum PasswordAlgorithmParameters {
  /// The Argon2id Algorithm, version 19
  Argon2idV19 {
    /// Time cost (iterations)
    t_cost: u32,

    /// Memory Cost, in multiples of 1KB, max 256MiB
    m_cost: u32,

    /// Allowed Parallelization
    p_cost: u32,
  },

  /// PBKDF2 HMAC Sha256 (RFC 2989)
  Pbkdf2HmacSha256 { iterations: u32 },
}

impl PasswordAlgorithmParameters {
  pub fn hash(
    &self,
    password: &[u8],
    salt: &[u8],
    digest: &mut [u8],
  ) -> Result<(), PasswordErr> {
    match self {
      PasswordAlgorithmParameters::Argon2idV19 {
        m_cost,
        t_cost,
        p_cost,
      } => {
        #[cfg(feature = "argon2")]
        {
          let params =
            argon2::Params::new(*m_cost, *t_cost, *p_cost, Some(digest.len()))
              .map_err(|_| PasswordErr::Argon2idV19ParametersUnsupported {
                m_cost:     *m_cost,
                t_cost:     *t_cost,
                p_cost:     *p_cost,
                digest_len: digest.len() as u32,
              })?;
          let hasher =
            argon2::Argon2::new(Algorithm::Argon2id, Version::V0x13, params);
          hasher
            .hash_password_into(password, salt.as_ref(), &mut digest[..])
            .log_err(Level::Trace)
            .map_err(|_| PasswordErr::Argon2idV19ParametersUnsupported {
              m_cost:     *m_cost,
              t_cost:     *t_cost,
              p_cost:     *p_cost,
              digest_len: digest.len() as u32,
            })?;
          Ok(())
        }
        #[cfg(not(feature = "argon2"))]
        {
          Err(PasswordErr::AlgorithmUnsupported(
            PasswordAlgorithm::Argon2idV19,
          ))
        }
      },
      PasswordAlgorithmParameters::Pbkdf2HmacSha256 { iterations } => {
        #[cfg(feature = "pbkdf2")]
        {
          // TODO: Error Handling
          pbkdf2::pbkdf2::<Hmac<sha2::Sha256>>(
            password,
            salt,
            *iterations,
            &mut digest[..],
          )
          .unwrap();
          Ok(())
        }
        #[cfg(not(feature = "pbkdf2"))]
        {
          Err(PasswordErr::AlgorithmUnsupported(
            PasswordAlgorithm::Pbkdf2HmacSha256,
          ))
        }
      },
    }
  }

  /// Reads the password algorithm and its parameters from a source byte byffer.
  // TODO: official documentation for password algorithm parameters
  // For now, just do the same ting here and in `parameters_write()`.
  fn from_parameter_data(
    algorithm_id: u16,
    source: &[u8],
  ) -> Result<Self, PasswordErr> {
    let algo = PasswordAlgorithm::try_from(algorithm_id)
      .map_err(|algo_id| PasswordErr::UnknownPasswordAlgorithm(algo_id))?;

    let cursor = &mut 0;
    match algo {
      PasswordAlgorithm::Argon2idV19 => {
        let t_cost = U32::bbrf(source, cursor)?.get();
        let m_cost = U32::bbrf(source, cursor)?.get();
        let p_cost = U32::bbrf(source, cursor)?.get();
        Ok(PasswordAlgorithmParameters::Argon2idV19 {
          t_cost,
          m_cost,
          p_cost,
        })
      },
      PasswordAlgorithm::Pbkdf2HmacSha256 => {
        let iterations = U32::bbrf(source, cursor)?.get();
        Ok(PasswordAlgorithmParameters::Pbkdf2HmacSha256 { iterations })
      },
      _ => Err(PasswordErr::AlgorithmUnsupported(algo)),
    }
  }

  /// Returns the number of bytes necessary to write the algorithm-specific
  /// parameters to a byte buffer.
  // TODO: official documentation for password algorithm parameters
  // For now, just do the same ting here and in `from_parameter_data()`.
  fn parameters_len(&self) -> usize {
    match self {
      PasswordAlgorithmParameters::Argon2idV19 { .. } => {
        // t_cost: U32, m_cost: U32, p_cost: U32
        size_of::<U32>() + size_of::<U32>() + size_of::<U32>()
      },
      PasswordAlgorithmParameters::Pbkdf2HmacSha256 { iterations } => {
        // iterations: U32
        size_of::<U32>()
      },
    }
  }

  /// Writes the algorithm-specific parameters to the target byte buffer
  fn parameters_write(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), BufferErr> {
    // TODO: official documentation for password algorithm parameters
    // For now, just do the same ting here and in `from_parameter_data()`.
    match self {
      PasswordAlgorithmParameters::Argon2idV19 {
        t_cost,
        m_cost,
        p_cost,
      } => {
        U32::from(*t_cost).bbwr(target, cursor)?;
        U32::from(*m_cost).bbwr(target, cursor)?;
        U32::from(*p_cost).bbwr(target, cursor)?;
        Ok(())
      },
      PasswordAlgorithmParameters::Pbkdf2HmacSha256 { iterations } => {
        U32::from(*iterations).bbwr(target, cursor)?;
        Ok(())
      },
    }
  }

  /// Returns the password algorithm identifier for this password.
  fn password_algorithm(&self) -> PasswordAlgorithm {
    match self {
      PasswordAlgorithmParameters::Argon2idV19 { .. } => {
        PasswordAlgorithm::Argon2idV19
      },
      PasswordAlgorithmParameters::Pbkdf2HmacSha256 { .. } => {
        PasswordAlgorithm::Pbkdf2HmacSha256
      },
      _ => PasswordAlgorithm::Unknown,
    }
  }
}

impl Password {
  /// Creates a new hash for the provided password (with a random salt)
  ///
  /// Requires the `alloc` feature because the `argon2` crate's `hash_raw`
  /// function returns a `Vec<u8>`.
  #[cfg(feature = "alloc")]
  pub fn new_default(
    password: &[u8],
    salt: &[u8],
  ) -> Result<Self, PasswordErr> {
    Self::new_argon2id(password, salt, None, None, None, None)
  }

  /// Creates a new salted password hash using the Argon2id algorithm,
  /// version 19.
  ///
  ///
  ///
  /// Paramters:
  /// - `salt`: A unique sequence of bytes used to prevent rainbow table attacks.
  /// - `password`: The plain text of the password.
  #[cfg(feature = "argon2")]
  pub fn new_argon2id(
    password: &[u8],
    salt: &[u8],
    digest_len: Option<u32>,
    m_cost: Option<u32>,
    t_cost: Option<u32>,
    p_cost: Option<u32>,
  ) -> Result<Self, PasswordErr> {
    let m_cost = m_cost.unwrap_or(argon2::Params::DEFAULT_M_COST);
    let t_cost = t_cost.unwrap_or(argon2::Params::DEFAULT_T_COST);
    let p_cost = p_cost.unwrap_or(argon2::Params::DEFAULT_P_COST);
    let digest_len = digest_len.unwrap_or(32);

    let mut digest = SmallVec::<u8, 32>::with_capacity(digest_len as usize);
    digest.extend(core::iter::repeat_n(0, digest_len as usize));

    let inner = PasswordAlgorithmParameters::Argon2idV19 {
      t_cost,
      m_cost,
      p_cost,
    };
    inner.hash(password, salt, &mut digest)?;

    Ok(Self {
      salt: SmallVec::<u8, 16>::from_slice(salt),
      digest,
      inner,
    })
  }

  pub fn new_pbkdf2_hmac_sha256(
    password: &[u8],
    salt: &[u8],
    digest_len: Option<u32>,
    iterations: Option<u32>,
  ) -> Result<Self, PasswordErr> {
    let digest_len = digest_len.unwrap_or(32);
    let mut digest = SmallVec::<u8, 32>::with_capacity(digest_len as usize);
    digest.extend(core::iter::repeat_n(0, digest_len as usize));

    let iterations = iterations.unwrap_or(10_000);
    let inner = PasswordAlgorithmParameters::Pbkdf2HmacSha256 { iterations };
    inner.hash(password, salt, &mut digest)?;

    Ok(Self {
      salt: SmallVec::<u8, 16>::from_slice(salt),
      digest,
      inner,
    })
  }

  /// Returns `true` iff the provided password matches.
  pub fn matches(&self, password: &[u8]) -> Result<bool, PasswordErr> {
    let mut digest = self.digest.clone();
    digest.fill(0);

    self.inner.hash(password, &self.salt, &mut digest)?;
    Ok(digest.as_slice() == self.digest.as_slice())
  }
}

impl ToGlyph for Password {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    GlyphHeader::new(
      GlyphType::PasswordHash,
      self.glyph_len().saturating_sub(size_of::<GlyphHeader>()),
    )?
    .bbwr(target, cursor)?;
    PasswordGlyphHeader::new(
      self.inner.password_algorithm(),
      self.salt.len(),
      self.digest.len(),
    )?
    .bbwr(target, cursor)?;
    u8::bbwrs(self.salt.as_ref(), target, cursor)?;
    u8::bbwrs(self.digest.as_ref(), target, cursor)?;
    pad_to_word(target, cursor)?;
    self.inner.parameters_write(target, cursor)?;
    pad_to_word(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<PasswordGlyphHeader>()
      + round_to_word(self.salt.len() + self.digest.len())
      + round_to_word(self.inner.parameters_len())
  }
}

impl<'a, G: Deref<Target = Glyph>> TryFrom<&'a PasswordGlyph<G>> for Password {
  type Error = PasswordErr;

  fn try_from(source: &'a PasswordGlyph<G>) -> Result<Self, Self::Error> {
    let salt = SmallVec::<u8, 16>::from_slice(source.salt());
    let digest = SmallVec::<u8, 32>::from_slice(source.digest());
    let inner = PasswordAlgorithmParameters::from_parameter_data(
      source.header().algorithm_id.get(),
      source.parameter_data(),
    )?;

    Ok(Self {
      salt,
      digest,
      inner,
    })
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
}

impl PasswordGlyphHeader {
  /// Creates a new `PasswordGlyphHeader` with the specified parameters.
  pub fn new(
    algorithm: PasswordAlgorithm,
    salt_len: usize,
    digest_len: usize,
  ) -> Result<Self, PasswordErr> {
    let salt_len = u8::try_from(salt_len)
      .map_err(|_| PasswordErr::UnsupportedSaltLen(salt_len))?;
    let digest_len = u8::try_from(digest_len)
      .map_err(|_| PasswordErr::UnsupportedDigestLen(digest_len))?;

    Ok(Self {
      algorithm_id: U16::from(algorithm as u16),
      salt_len,
      digest_len,
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

/// A list of supported encrypted password types.
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum PasswordAlgorithm {
  // SAFETY: IDs must be continuous, and Self::MAX_ID must always be updated
  /// The type of algorithm used to hash this password is not known.
  Unknown = 0x0000,

  /// The Argon2id Password Hashing Algorithm, with user-specified parameters
  /// for memory, iteration, and parallelization costs.
  ///
  /// A modern (a/o 2025) high-security standard, but not feasible in all
  /// contexts (i.e., embedded).
  Argon2idV19 = 0x0001,

  /// PBKDF2 HMAC Sha256
  ///
  /// See [RFC 2989](https://tools.ietf.org/html/rfc2898) and the
  /// [`pbkdf2` crate](https://docs.rs/pbkdf2/latest/pbkdf2/).
  Pbkdf2HmacSha256 = 0x0002,
}

impl PasswordAlgorithm {
  const MAX_ID: u16 = Self::Pbkdf2HmacSha256 as u16;

  pub fn try_from(value: u16) -> Result<Self, u16> {
    if value <= Self::MAX_ID {
      unsafe { Ok(transmute(value)) }
    } else {
      Err(value)
    }
  }
}

impl From<u16> for PasswordAlgorithm {
  fn from(src: u16) -> Self {
    if src > Self::MAX_ID {
      Self::Unknown
    } else {
      unsafe { transmute::<u16, Self>(src) }
    }
  }
}

pub struct PasswordGlyph<G: Deref<Target = Glyph>> {
  glyph:         G,
  salt_offset:   usize,
  digest_offset: usize,
}

impl<G: Deref<Target = Glyph>> PasswordGlyph<G> {
  fn header(&self) -> &PasswordGlyphHeader {
    let content = self.glyph.content_padded();
    // SAFETY: Infallible b/c/o bounds check in `from_glyph`.
    unsafe { PasswordGlyphHeader::bbrf_u(content, &mut 0) }
  }

  /// Returns the algorithm used to encrypt the password.
  pub fn algorithm(&self) -> PasswordAlgorithm {
    self.header().algorithm()
  }

  /// Returns the salt used before calculating the password digest.
  pub fn salt(&self) -> &[u8] {
    let header = self.header();
    // SAFETY: Infallible b/c/o bounds check in `from_glyph`.
    unsafe {
      u8::bbrfs_u(
        self.glyph.content_padded(),
        &mut self.salt_offset.clone(),
        header.salt_len(),
      )
    }
  }

  /// Returns the digest of the salted password
  pub fn digest(&self) -> &[u8] {
    let header = self.header();
    // SAFETY: Infallible b/c/o bounds check in `from_glyph`.
    unsafe {
      u8::bbrfs_u(
        self.glyph.content_padded(),
        &mut self.digest_offset.clone(),
        header.digest_len(),
      )
    }
  }

  /// Decodes the `Password` stored in this glyph.
  pub fn password(&self) -> Result<Password, PasswordErr> {
    Password::try_from(self)
  }

  /// Returns `true` if the provided password matches.
  pub fn matches(&self, password: &[u8]) -> Result<bool, GlyphErr> {
    let pw = self.password()?;
    todo!()
  }

  fn parameter_data(&self) -> &[u8] {
    todo!()
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for PasswordGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(glyph: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    // SAFETY: Guaranteed bounds checks for header, salt, and digest.

    let parse_result: Result<_, GlyphErr> = (|| {
      let content = glyph.content();
      let cursor = &mut 0;
      glyph.header().confirm_type(GlyphType::PasswordHash)?;
      let pw_header = PasswordGlyphHeader::bbrd(content, cursor)?;
      let salt_offset = *cursor;
      *cursor += pw_header.salt_len();
      let digest_offset = *cursor;
      *cursor += pw_header.digest_len();
      bounds_check(content, *cursor)?;
      Ok((salt_offset, digest_offset))
    })();

    match parse_result {
      Ok((salt_offset, digest_offset)) => Ok(Self {
        glyph,
        salt_offset,
        digest_offset,
      }),
      Err(err) => Err(DecodeErr::new(glyph, err)),
    }
  }
}

impl<G: Deref<Target = Glyph>> Debug for PasswordGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("PasswordGlyph");
    df.field("salt", &ShortHexDump(self.salt(), 0));
    df.field("digest", &ShortHexDump(self.digest(), 0));
    df.field("algorithm", &self.algorithm());
    // FIXME: Password inner (or unknown)
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for PasswordGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> Eq for PasswordGlyph<G> {}

impl<G: Deref<Target = Glyph>> PartialOrd for PasswordGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for PasswordGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, GlyphSorting::default())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for PasswordGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::TypeAndBytes => {
        let a = self.glyph.deref();
        let b = other.glyph.deref();
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum PasswordErr {
  BufferErr(BufferErr),
  UnknownPasswordAlgorithm(u16),

  /// The hashing algorithm is known but not supported on this platform.
  ///
  /// This may be caused, e.g., if the memory or processing requirements cannot
  /// be feasibly supported with available hardware.
  AlgorithmUnsupported(PasswordAlgorithm),

  /// The hashing algorithm is supported, but not with the specified parameters.
  ///
  /// If the value of `memory_cost` or `cpu_cost` is either 0 or `u32::MAX`,
  /// this specifies an error
  Argon2idV19ParametersUnsupported {
    m_cost:     u32,
    t_cost:     u32,
    p_cost:     u32,
    digest_len: u32,
  },

  InternalError(PasswordAlgorithm),
  UnsupportedSaltLen(usize),
  UnsupportedDigestLen(usize),
  /// FIXME: internal error, not tied to a password algorithm…
  InternalErrorGlyphs,
}

impl From<BufferErr> for PasswordErr {
  fn from(err: BufferErr) -> Self {
    Self::BufferErr(err)
  }
}

impl From<PasswordErr> for GlyphErr {
  fn from(value: PasswordErr) -> Self {
    GlyphErr::PasswordErr(value)
  }
}

#[cfg(test)]
#[allow(unused)]
mod test {
  use super::*;
  use crate::util::test::{init_test_logger, TEST_PLAINTEXT};
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  // FIXME
  // #[test]
  // fn passwords() {
  //   init_test_logger();
  //
  //   //== Correct function of `Password` ==//
  //   let pw1 = b"hunter2";
  //   let pw2 = b"correcthorsebatterystaple";
  //
  //   let mut rng = ChaCha20Rng::from_seed([32; 32]);
  //   let epw1 = Password::new_argon2id(pw1, &mut rng).unwrap();
  //   let epw2 = Password::new_argon2id(pw2, &mut rng).unwrap();
  //
  //   assert!(epw1.matches(pw1).unwrap());
  //   assert!(!epw1.matches(pw2).unwrap());
  //   assert!(epw2.matches(pw2).unwrap());
  //   assert!(!epw2.matches(pw1).unwrap());
  //
  //   //== Round Trip Codec of `Password` into `PasswordGlyph` ==//
  //   let g = Glyph::new(&epw1).unwrap();
  //   std::dbg!(&g);
  //   let pwg = PasswordGlyph::from_glyph(g).unwrap();
  //   dbg!(&pwg);
  //   let epw1_2 = pwg.password().unwrap();
  //   assert_eq!(epw1, epw1_2);
  //
  //   //== Operation of password checking directly from `PasswordGlyph` ==//
  //   assert!(pwg.matches(pw1).unwrap());
  //   assert!(!pwg.matches(pw2).unwrap());
  // }

  // #[test]
  // fn crypto_password_key() -> Result<(), GlyphErr> {
  //   init_test_logger();
  //
  //   let mut rng = ChaCha20Rng::from_seed([32; 32]);
  //   let key = PasswordKey::new(b"hunter2")?;
  //
  //   let mut message: alloc::boxed::Box<[u8]> =
  //     alloc::boxed::Box::try_from(&TEST_PLAINTEXT[..])?;
  //   dbg!(ShortHexDump(message.as_ref(), 8));
  //
  //   let (_ct_hash, md) = key.encrypt(&mut rng, message.as_mut())?;
  //   dbg!(ShortHexDump(message.as_ref(), 8));
  //
  //   key.decrypt(&md, message.as_mut())?;
  //   dbg!(ShortHexDump(message.as_ref(), 8));
  //
  //   assert_eq!(message.as_ref(), &TEST_PLAINTEXT[..]);
  //
  //   Ok(())
  // }
}
