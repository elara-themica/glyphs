//! Contains the GLIFS-internal interface to cryptographic hashing functions.
//!
//! Note that GLIFS itself does not contain any cryptographic code, but does
//! have its own internal API to those functions in anticipation of using
//! implementations from different places (e.g., where OpenSSL may not always
//! be available)

use crate::{
  glyph::{Glyph, GlyphType},
  util::debug::ShortHexDump,
  zerocopy::{InBasicVec, ZeroCopy, BasicVecType, U16},
  DecodeErr, EncodedGlyph, FromGlyph, GlyphErr, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::transmute,
};
use std::{cmp::Ordering, ops::Deref};

/// The default cryptographic hash for glyphs.
pub type GlyphHash = blake3::Blake3Hash;
/// The default cryptographic hash context for glyphs.
pub type GlyphHashContext = blake3::Blake3Context;

/// Glyphs trait for cryptographic hash functions.
///
/// Requirements:
///
/// - The hash digest must be at least 16 bytes.  E.g., CRC-32 might be useful
///   for error correction, but should not be used for cryptographic purposes.
pub trait CryptographicHash:
  ZeroCopy
  + Default
  + AsRef<[u8]>
  + AsMut<[u8]>
  + ToGlyph
  + for<'a> FromGlyph<&'a Glyph>
  + for<'a> TryFrom<&'a [u8], Error=HashErr>
  + Send
  + Sync
  + 'static
{
  /// The length of the hash produced by the function, in bytes.
  const HASH_LEN: usize;

  /// The glyph hash type ID associated with this type of cryptographic hash.
  ///
  /// See [`CryptoHashType`].
  const HASH_TYPE_ID: CryptoHashType;

  /// The type used for generating more hashes of this type.
  type Context: HashContext<Output = Self>;

  /// Calculate a new hash of this type from the byte slice provided.
  ///
  /// Note that, if you need to include more than just a single byte slice,
  /// you'll need to use this type's hash context instead.
  fn new(bytes: &[u8]) -> Self {
    let mut context = <Self as CryptographicHash>::Context::new();
    context.update(bytes.as_ref());
    context.finish()
  }

  /// The raw hash bytes.
  fn hash_bytes(&self) -> &[u8];

  /// Returns the last 4 bytes of the hash.
  fn suffix_bytes(&self) -> [u8; 4];

  /// Create a new random hash.
  #[cfg(feature = "rand")]
  fn random<R: rand::Rng>(rng: &mut R) -> Self
  {
    let mut hash = Self::default();
    rng.fill_bytes(hash.as_mut());
    hash
  }

  /// An instance of the hash with all zeroes.
  ///
  /// This will typically be the same as the hash returned by
  /// `Default::default()`, but the `Default` trait does not formally require
  /// this.
  fn zero() -> Self {
    let mut hash = Self::default();
    hash.as_mut().fill(0);
    hash
  }
}

/// An internal trait for cryptographic hash contexts.
pub trait HashContext {
  /// The type of output returned by this hash context
  type Output;

  /// Creates a new context
  fn new() -> Self;

  /// Update the context with additional data
  fn update(&mut self, bytes: &[u8]);

  /// Complete the calculation and return the hash value
  fn finish(self) -> Self::Output;
}

/// A header used to identify a type of cryptographic hash.
#[repr(packed)]
#[derive(Copy, Clone)]
pub struct CryptoHashHeader {
  hash_type_id: U16,
  reserved:     [u8; 2],
}

impl CryptoHashHeader {
  /// Creates a new header.
  pub fn new<H: CryptographicHash>() -> Self {
    Self {
      hash_type_id: H::HASH_TYPE_ID.into(),
      reserved:     Default::default(),
    }
  }

  /// Returns the type of cryptographic hash.
  pub fn hash_type(&self) -> CryptoHashType {
    CryptoHashType::from(self.hash_type_id)
  }

  /// Returns an error if the header's hash type doesn't match that provided.
  pub fn confirm_hash_type(
    &self,
    hash_type: CryptoHashType,
  ) -> Result<(), GlyphErr> {
    if hash_type == self.hash_type() {
      Ok(())
    } else {
      Err(GlyphErr::UnexpectedCryptoHashType {
        expected: hash_type,
        observed: self.hash_type(),
      })
    }
  }
}

unsafe impl ZeroCopy for CryptoHashHeader {}

/// Identifies the types of cryptographic hashes.
#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum CryptoHashType {
  /// Unspecified
  Unspecified = 0x0000,
  /// MD5
  MD5 = 0x0001,
  /// SHA-1
  SHA1 = 0x0002,
  /// SHA2-256
  SHA256 = 0x0003,
  /// SHA2-512,
  SHA512 = 0x0004,
  /// SHA3-256
  SHA3 = 0x0005,

  /// Blake3
  Blake3 = 0x0006,

  // This must always be the last member.
  /// Unknown
  Unknown = 0x0007,
}

impl From<u16> for CryptoHashType {
  fn from(value: u16) -> Self {
    unsafe {
      if value > CryptoHashType::Unknown as u16 {
        CryptoHashType::Unknown
      } else {
        transmute::<u16, CryptoHashType>(value)
      }
    }
  }
}

impl From<U16> for CryptoHashType {
  fn from(value: U16) -> Self {
    value.get().into()
  }
}

impl From<CryptoHashType> for u16 {
  fn from(value: CryptoHashType) -> Self {
    value as u16
  }
}

impl From<CryptoHashType> for U16 {
  fn from(value: CryptoHashType) -> Self {
    U16::from(value as u16)
  }
}

/// Glyph containing one or more cryptographic hashes.
pub struct HashGlyph<G: Deref<Target = Glyph>>(G, *const [u8]);

impl<G: Deref<Target = Glyph>> HashGlyph<G> {
  /// The old_crypto hash header.
  fn header(&self) -> &CryptoHashHeader {
    // SAFETY: `from_glyph` creation guarantees valid header.
    unsafe {
      let content = self.0.content();
      let cursor = &mut 0;
      CryptoHashHeader::bbrf_u(content, cursor)
    }
  }

  /// Returns the type of hash stored in the glyph.
  pub fn hash_type(&self) -> CryptoHashType {
    self.header().hash_type()
  }

  pub fn digest_bytes(&self) -> &[u8] {
    unsafe { &*self.1 }
  }

  pub fn get<H: CryptographicHash>(&self) -> Result<&H, GlyphErr> {
    self.header().confirm_hash_type(H::HASH_TYPE_ID)?;
    let hash = H::bbrf(self.digest_bytes(), &mut 0)?;
    Ok(hash)
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for HashGlyph<G> {
  type Error = GlyphErr;

  fn from_glyph(glyph: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    /* SAFETY: We're going to guarantee that contents contain at least a header,
               to avoid duplicate bounds checks.
    */
    if let Err(err) = glyph.header().confirm_type(GlyphType::CryptoHash) {
      return Err(DecodeErr::new(glyph, err));
    }
    let content = glyph.content();
    let cursor = &mut 0;
    let _header = match CryptoHashHeader::bbrf(content, cursor) {
      Ok(header) => header,
      Err(err) => return Err(DecodeErr::new(glyph, err.into())),
    };
    let digest_bytes = &content[*cursor..] as *const [u8];
    Ok(Self(glyph, digest_bytes))
  }
}

impl<'a> HashGlyph<&'a Glyph> {
  pub fn digest_bytes_parsed(&self) -> &'a [u8] {
    unsafe { &*self.1 }
  }

  pub fn get_parsed<H: CryptographicHash>(&self) -> Result<&'a H, GlyphErr> {
    self.header().confirm_hash_type(H::HASH_TYPE_ID)?;
    let hash = H::bbrf(self.digest_bytes_parsed(), &mut 0)?;
    Ok(hash)
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for HashGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> Eq for HashGlyph<G> {}

impl<G: Deref<Target = Glyph>> PartialOrd for HashGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<G: Deref<Target = Glyph>> Ord for HashGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> Debug for HashGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    match self.hash_type() {
      CryptoHashType::Unspecified => {
        write!(f, "UnspecifiedHashGlyph(")?;
      },
      CryptoHashType::MD5 => {
        write!(f, "MD5Glyph(")?;
      },
      CryptoHashType::SHA1 => {
        write!(f, "SHA1Glyph(")?;
      },
      CryptoHashType::SHA256 => {
        write!(f, "SHA2Glyph(")?;
      },
      CryptoHashType::SHA512 => {
        write!(f, "SHA2_512Glyph(")?;
      },
      CryptoHashType::SHA3 => {
        write!(f, "SHA3Glyph(")?;
      },
      CryptoHashType::Blake3 => {
        write!(f, "Blake3Glyph(")?;
      },
      CryptoHashType::Unknown => {
        write!(f, "UnknownHashGlyph(")?;
      },
    }
    write!(f, "{:?})", &ShortHexDump(self.digest_bytes(), 0))?;
    Ok(())
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for HashGlyph<G> {
  fn into_inner(self) -> G {
    self.0
  }

  fn glyph(&self) -> &Glyph {
    &self.0
  }
}

/// A CIDR-like prefix for cryptographic hashes.
///
/// - The maximum length of the prefix is 120 bits.
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
#[repr(packed)]
// SAFETY: We depend on this repr and layout because we interpret as an U128.
pub struct HashPrefix {
  prefix:     [u8; 15],
  prefix_len: u8,
}

/// A matching prefix for cryptographic hashes, analogous to a CIDR netmask.
impl HashPrefix {
  /// The default prefix matching all hashes, i.e., `::/0`
  const DEFAULT: HashPrefix = HashPrefix {
    prefix:     [0u8; 15],
    prefix_len: 0,
  };
  const MAX_PREFIX_LEN: usize = 120;

  /// Creates a new hash prefix.
  ///
  /// Parameters:
  /// - `hash`: The bytes of the hash.  Only the first `mask_len` bits will be
  ///   used.
  /// - `mask_len`: The number of bits in the prefix. If the value is greater
  ///   than 248, it will be truncated to 248.
  pub fn new(hash: &[u8], mask_len: usize) -> Self {
    let prefix_len = mask_len.min(120);
    let prefix_mask = (!(u128::MAX >> prefix_len)).to_be_bytes();
    let mut prefix = [0u8; 15];
    for (dst, (src, mask)) in
      prefix.iter_mut().zip(hash.iter().zip(prefix_mask.iter()))
    {
      *dst = *src & *mask;
    }
    Self {
      prefix,
      prefix_len: prefix_len as u8,
    }
  }

  /// For working with the prefix as a big-endian u128.
  ///
  /// This loads the u128 from the prefix, as if it were a big-endian u128.
  /// However, remember that this must be converted back to big-endian bytes
  /// if you need to write hash data back into a byte buffer.
  fn as_u128(&self) -> u128 {
    u128::from_be_bytes([
      self.prefix[0], self.prefix[1], self.prefix[2], self.prefix[3],
      self.prefix[4], self.prefix[5], self.prefix[6], self.prefix[7],
      self.prefix[8], self.prefix[9], self.prefix[10], self.prefix[11],
      self.prefix[12], self.prefix[13], self.prefix[14], 0])
  }

  /// Returns the number of bits in the hash mask.
  pub fn prefix_len(&self) -> usize {
    self.prefix_len as usize
  }

  /// Returns a byte slice of the hash prefix.
  ///
  /// Note that only the first `prefex_len()` bits should be compared.
  pub fn prefix_bytes(&self) -> &[u8] {
    &self.prefix[..]
  }

  /// Creates a new `HashPrefix` with an `bits` additional bits of specificity.
  ///
  /// For example, if the original prefix is `7200::/8`, and this function is
  /// called with `bits = 4, number = 14`, the resulting prefix would be
  /// `72e0::/12`.
  ///
  // TODO: Fix, tests, and documentation.
  pub fn child(&self, add_bits: usize, nth: usize) -> Result<Self, GlyphErr> {
    if self.prefix_len as usize + add_bits > Self::MAX_PREFIX_LEN {
      return Err(GlyphErr::InvalidHashPrefixLen(
        self.prefix_len as usize + add_bits,
      ));
    }

    let mut prefix = self.as_u128();
    let nth_mask = u128::MAX >> 128usize.saturating_sub(add_bits);
    let nth = (nth as u128) & nth_mask;
    let nth_bits = nth
      << 128usize
        .saturating_sub(add_bits)
        .saturating_sub(self.prefix_len());
    prefix |= nth_bits;

    let tmp = prefix.to_be_bytes();
    let mut prefix_bytes = [0u8; 15];
    for (src, dst) in tmp.iter().zip(prefix_bytes.iter_mut()) {
      *dst = *src;
    }
    let mask_len = self.prefix_len().saturating_add(add_bits).min(120) as u8;

    Ok(Self {
      prefix:     prefix_bytes,
      prefix_len: mask_len,
    })
  }

  /// Given this hash prefix and `2^bits` sub-prefix children, determine the
  /// observed child index of an observed hash.
  ///
  /// For example, if the has prefix is `5000::/4`, and our sub-hashes will use
  /// an additional `4` bytes (i.e., `5000::/8`, `5100::/8`, `5200::/8`, etc...,
  /// then an observed hash that starts with `5A29...`, then the child index
  /// of this hash will be 10 (0xA).
  // LATER: Improve error checking and documentation
  #[inline]
  pub fn which_child(
    &self,
    hash: &[u8],
    bits: usize,
  ) -> Result<usize, GlyphErr> {
    let mut tmp = [0u8; 16];
    for (src, dst) in hash.iter().zip(tmp.iter_mut()) {
      *dst = *src;
    }
    let hash = u128::from_be_bytes(tmp);
    let n_mask =
      (u128::MAX << 128usize.saturating_sub(bits)) >> self.prefix_len() as u128;
    let n = (hash & n_mask)
      >> 128usize
        .saturating_sub(self.prefix_len())
        .saturating_sub(bits);
    Ok(n as usize)
  }

  /// Returns true iff `hash_bytes` matches this prefix.
  //
  // TODO: Write tests.
  pub fn matches(&self, hash_bytes: &[u8]) -> bool {
    //== Convert both to u128s ==//
    let prefix = self.as_u128();

    let mut tmp = [0u8; 16];
    for (src, dst) in hash_bytes.iter().zip(tmp.iter_mut()) {
      *dst = *src;
    }
    let hash = u128::from_be_bytes(tmp);
    let prefix_mask = u128::MAX << 128 - self.prefix_len() as u128;
    let prefix = prefix & prefix_mask;
    let hash = hash & prefix_mask;
    prefix == hash
  }

  /// Returns the lower bound of the hash prefix, like the CIDR network address.
  ///
  /// - Any bits after `self.length()` will be set to zero.
  /// - Unlike [`Self::lower_bound()`], we can return a reference because the
  ///   internal storage is a fixed-length CIDR-like format.
  // TODO: Test and better docs
  pub fn lower_bound<H: CryptographicHash>(self) -> H
  {
    let num = self.as_u128();
    let mask = if self.prefix_len == 0 {
      0u128
    } else {
      // Need to use signed integers for arithmetic vs. logical shift
      let mask = i128::MIN >> (self.prefix_len - 1);
      mask as u128
    };
    let masked = num & mask;
    let mut hash = H::default();
    let hash_bytes = hash.as_mut();
    hash_bytes.copy_from_slice(masked.to_be_bytes().as_ref());
    hash
  }

  /// Returns the upper bounds of the hash prefix, like a CIDR broadcast
  /// address.
  ///
  /// - Any bits after `self.length()` will be set to one.
  /// - Unlike [`Self::lower_bound()`], we cannot return a reference because the
  ///   internal storage is a fixed-length CIDR-like format.
  // TODO: Test and better docs
  pub fn upper_bound<H: CryptographicHash>(self) -> H
  {
    let num = self.as_u128();
    let mask = u128::MAX >> self.prefix_len();
    let masked = num | mask;

    let mut hash = H::default();
    let hash_bytes = hash.as_mut();
    hash_bytes.copy_from_slice(masked.to_be_bytes().as_ref());
    hash
  }

  /// The number of bits in the prefix.
  pub fn length(&self) -> usize {
    self.prefix_len as usize
  }
}

/// SAFETY: Byte arrays are inherently zero copy.
unsafe impl ZeroCopy for HashPrefix {}

impl InBasicVec for HashPrefix {
  const BASIC_VEC_TYPE: BasicVecType = BasicVecType::HashPrefix;
}

impl Debug for HashPrefix {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    if !f.alternate() {
      write!(
        f,
        "{:030x?}/{}",
        &ShortHexDump(&self.prefix[..], 32),
        &self.prefix_len()
      )
    } else {
      write!(
        f,
        "HashPrefix({:030x?}/{})",
        &ShortHexDump(&self.prefix[..], 32),
        &self.prefix_len()
      )
    }
  }
}

// TODO
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum HashErr {
  /// Attempt to read a hash from a byte buffer shorter than the hash digest.
  ReadUnderflow {
    expected: usize,
    observed: usize,
  },

  /// Attempt to read a hash from a byte buffer longer than the hash digest.
  ReadOverflow{
    expected: usize,
    observed: usize,
  },

  /// Errors caused by bugs in the
  InternalErr,

}

// TODO: Test implementing these from another crate, and fully convert trait
//       call reference style to
macro_rules! hash_impls {
  ($hash_name:ident, $hash_len:expr, $hash_tid:ident, $zc_tid:ident, $context_name:ident) => {
    unsafe impl $crate::zerocopy::ZeroCopy for $hash_name {}

    impl $crate::zerocopy::InBasicVec for $hash_name {
      const BASIC_VEC_TYPE: $crate::zerocopy::BasicVecType =
        $crate::zerocopy::BasicVecType::$zc_tid;
    }

    impl $crate::crypto::CryptographicHash for $hash_name {
      type Context = $context_name;

      const HASH_LEN: usize = $hash_len;
      const HASH_TYPE_ID: $crate::crypto::CryptoHashType =
        $crate::crypto::CryptoHashType::$hash_tid;

      fn hash_bytes(&self) -> &[u8] {
        &self.0[..]
      }

      fn suffix_bytes(&self) -> [u8; 4] {
        [
          self.0[Self::HASH_LEN - 4],
          self.0[Self::HASH_LEN - 3],
          self.0[Self::HASH_LEN - 2],
          self.0[Self::HASH_LEN - 1],
        ]
      }
    }

    impl<'a> TryFrom<&'a [u8]> for $hash_name {
      type Error = HashErr;
      fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        match bytes.len().cmp(&($hash_name::HASH_LEN)) {
          core::cmp::Ordering::Less => Err(HashErr::ReadUnderflow { expected: Self::HASH_LEN, observed: bytes.len()}),
          core::cmp::Ordering::Greater => Err(HashErr::ReadOverflow { expected: Self::HASH_LEN, observed: bytes.len()}),
          core::cmp::Ordering::Equal => {
            let mut hash = Self::default();
            hash.as_mut().copy_from_slice(&bytes);
            Ok(hash)
          }
        }
      }
    }

    /// The default value is all zeroes.
    impl core::default::Default for $hash_name {
      fn default() -> Self {
        Self([0u8; $hash_len])
      }
    }

    impl core::convert::AsRef<[u8]> for $hash_name {
      fn as_ref(&self) -> &[u8] {
        &self.0[..]
      }
    }

    impl core::convert::AsMut<[u8]> for $hash_name {
      fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0[..]
      }
    }

    impl core::fmt::Debug for $hash_name {
      fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
          f,
          "{}({})",
          stringify!($hash_name),
          &$crate::util::debug::ShortHexDump(&self.0[..], 128)
        )
      }
    }

    impl core::fmt::Display for $hash_name {
      fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(
          &$crate::util::debug::ShortHexDump(&self.0[..], 128),
          f,
        )
      }
    }

    impl $crate::ToGlyph for $hash_name {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), $crate::GlyphErr> {
        let content_len = $crate::zerocopy::round_to_word(
          core::mem::size_of::<$crate::crypto::CryptoHashHeader>()
            + core::mem::size_of::<$hash_name>(),
        );
        let glyph_header =
          $crate::GlyphHeader::new($crate::GlyphType::CryptoHash, content_len)?;
        $crate::zerocopy::ZeroCopy::bbwr(&glyph_header, target, cursor)?;
        let hash_header = $crate::crypto::CryptoHashHeader::new::<$hash_name>();
        $crate::zerocopy::ZeroCopy::bbwr(&hash_header, target, cursor)?;
        $crate::zerocopy::ZeroCopy::bbwr(self, target, cursor)?;
        $crate::zerocopy::pad_to_word(target, cursor)?;
        Ok(())
      }

      fn glyph_len(&self) -> usize {
        core::mem::size_of::<$crate::GlyphHeader>()
          + $crate::zerocopy::round_to_word(
            core::mem::size_of::<$crate::crypto::CryptoHashHeader>()
              + core::mem::size_of::<$hash_name>(),
          )
      }
    }

    impl<G: Deref<Target = $crate::Glyph>> $crate::FromGlyph<G> for $hash_name {
      type Error = $crate::GlyphErr;

      fn from_glyph(
        glyph: G,
      ) -> Result<Self, $crate::DecodeErr<G, Self::Error>> {
        match $crate::crypto::HashGlyph::<_>::from_glyph(glyph) {
          Ok(hg) => match hg.get::<$hash_name>() {
            Ok(hash) => Ok(*hash),
            Err(err) => return Err(DecodeErr::new(hg.0, err)),
          },
          Err(err) => Err(err),
        }
      }
    }

    gen_prim_slice_to_glyph!($hash_name);
    gen_prim_slice_from_glyph_parsed!($hash_name);
  };
}

pub(crate) mod md5 {
  use super::*;

  /// The length of a MD5 hash value, in bytes (=16)
  pub const MD5_DIGEST_BYTES: usize = 16;

  /// An MD5 hash value
  ///
  /// The MD5 hashing algorithm should be considered to be
  /// [insecure](https://en.wikipedia.org/wiki/MD5#Security) and should not
  /// be used in applications where a hash collision would represent a security
  /// issue.
  #[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
  #[repr(C)]
  pub struct Md5Hash(pub [u8; MD5_DIGEST_BYTES]);

  /// A context for calculating an MD5 hash
  pub struct Md5Context(::md5::Context);
  impl HashContext for Md5Context {
    type Output = Md5Hash;

    fn new() -> Self {
      Md5Context(::md5::Context::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      self.0.consume(bytes);
    }

    fn finish(self) -> Self::Output {
      let result = self.0.compute();
      Md5Hash(result.0)
    }
  }

  hash_impls!(Md5Hash, MD5_DIGEST_BYTES, MD5, HashMD5, Md5Context);
}

pub(crate) mod sha1 {
  use super::*;
  #[rustfmt::skip]
  use ::sha1::Digest;

  /// The length of a SHA-1 hash value, in bytes (=20)
  pub const SHA1_DIGEST_BYTES: usize = 20;

  /// A SHA-1 hash value
  #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(packed)]
  pub struct Sha1Hash([u8; SHA1_DIGEST_BYTES]);

  /// A context for calculating an SHA-1 hash
  #[cfg(feature = "sha1")]
  pub struct Sha1Context(::sha1::Sha1);

  #[cfg(feature = "sha1")]
  impl HashContext for Sha1Context {
    type Output = Sha1Hash;

    fn new() -> Self {
      Sha1Context(::sha1::Sha1::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      use ::sha1::Digest;
      self.0.update(bytes);
    }

    fn finish(self) -> Self::Output {
      use ::sha1::Digest;
      let output = self.0.finalize();
      let mut hash_bytes = [0u8; 20];
      hash_bytes.clone_from_slice(output.as_slice());
      Sha1Hash(hash_bytes)
    }
  }

  hash_impls!(Sha1Hash, SHA1_DIGEST_BYTES, SHA1, HashSHA1, Sha1Context);
}

pub(crate) mod sha256 {
  use super::*;
  #[rustfmt::skip]
  use ::sha2::Digest;

  /// The length of a SHA-2 256 byte hash value, in bytes (=32)
  pub const SHA_256_DIGEST_BYTES: usize = 32;

  /// A SHA-2 256-bit hash value
  #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(packed)]
  pub struct Sha256Hash(pub [u8; SHA_256_DIGEST_BYTES]);

  /// A context for calculating a SHA-2 256-bit hash
  #[cfg(feature = "sha2")]
  #[derive(Clone)]
  pub struct Sha256Context(::sha2::Sha256);

  #[cfg(feature = "sha2")]
  impl HashContext for Sha256Context {
    type Output = Sha256Hash;

    fn new() -> Self {
      Sha256Context(::sha2::Sha256::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      use ::sha2::Digest;
      self.0.update(bytes);
    }

    fn finish(self) -> Self::Output {
      use ::sha2::Digest;
      let output = self.0.finalize();
      let mut hash_bytes = [0u8; 32];
      hash_bytes.clone_from_slice(output.as_slice());
      Sha256Hash(hash_bytes)
    }
  }

  hash_impls!(
    Sha256Hash,
    SHA_256_DIGEST_BYTES,
    SHA256,
    HashSHA2,
    Sha256Context
  );
}

pub(crate) mod sha512 {
  use super::*;

  /// The length of an SHA-2 256 byte hash value, in bytes (=32)
  pub const SHA512_DIGEST_BYTES: usize = 64;

  /// A SHA-2 256-bit hash value
  #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(packed)]
  pub struct Sha512Hash(pub [u8; SHA512_DIGEST_BYTES]);

  /// A context for calculating a SHA-2 256-bit hash
  #[cfg(feature = "sha2")]
  #[derive(Clone)]
  pub struct Sha512Context(::sha2::Sha512);

  #[cfg(feature = "sha2")]
  impl HashContext for Sha512Context {
    type Output = Sha512Hash;

    fn new() -> Self {
      Sha512Context(<::sha2::Sha512 as ::sha2::Digest>::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      ::sha2::Digest::update(&mut self.0, bytes);
    }

    fn finish(self) -> Self::Output {
      use ::sha2::Digest;
      let output = self.0.finalize();
      let mut hash_bytes = [0u8; 64];
      hash_bytes.clone_from_slice(output.as_slice());
      Sha512Hash(hash_bytes)
    }
  }

  hash_impls!(
    Sha512Hash,
    SHA512_DIGEST_BYTES,
    SHA512,
    HashSHA512,
    Sha512Context
  );
}

pub(crate) mod sha3 {
  use super::*;
  use ::sha3::Digest;

  /// The length of a SHA-3 256-bit hash value, in bytes (=32)
  pub const SHA3_DIGEST_BYTES: usize = 32;

  /// A SHA-3 256-bit hash value
  #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(C)]
  pub struct Sha3Hash(pub [u8; SHA3_DIGEST_BYTES]);

  /// A context for calculating a SHA-3 256-bit hash
  #[cfg(feature = "sha3")]
  pub struct Sha3Context(::sha3::Sha3_256);

  #[cfg(feature = "sha3")]
  impl HashContext for Sha3Context {
    type Output = Sha3Hash;

    fn new() -> Self {
      Sha3Context(::sha3::Sha3_256::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      self.0.update(bytes)
    }

    fn finish(self) -> Self::Output {
      let hash = self.0.finalize();
      Sha3Hash(hash.into())
    }
  }

  hash_impls!(Sha3Hash, SHA3_DIGEST_BYTES, SHA3, HashSHA3, Sha3Context);
}

pub(crate) mod blake3 {
  use super::*;

  /// The length of a Blake3 256-bit hash value, in bytes
  pub const BLAKE3_DIGEST_BYTES: usize = 32;

  /// A Blake3 256-bit hash value
  #[derive(Clone, Copy, Hash, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(transparent)]
  pub struct Blake3Hash(pub [u8; BLAKE3_DIGEST_BYTES]);

  /// A context for calculating a Blake3 256-bit hash
  pub struct Blake3Context(::blake3::Hasher);

  impl HashContext for Blake3Context {
    type Output = Blake3Hash;

    fn new() -> Self {
      Blake3Context(::blake3::Hasher::new())
    }

    fn update(&mut self, bytes: &[u8]) {
      self.0.update(bytes);
    }

    fn finish(self) -> Self::Output {
      let hash = self.0.finalize();
      Blake3Hash(hash.into())
    }
  }
  hash_impls!(
    Blake3Hash,
    BLAKE3_DIGEST_BYTES,
    Blake3,
    HashBlake3,
    Blake3Context
  );
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::{
    crypto::{
      blake3::Blake3Hash, md5::Md5Hash, sha1::Sha1Hash, sha256::Sha256Hash,
      sha3::Sha3Hash,
    },
    util::test::{
      init_test_logger, simple_codec_slice_test, simple_codec_test,
    },
  };
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[test]
  fn codec_hashes() {
    let mut rng = ChaCha20Rng::from_seed([0x42; 32]);

    #[cfg(feature = "md5")]
    {
      let hash = Md5Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Md5Hash, Md5Hash>(hash);
    }

    #[cfg(feature = "sha1")]
    {
      let hash = Sha1Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Sha1Hash, Sha1Hash>(hash);
    }

    #[cfg(feature = "sha2")]
    {
      let hash = Sha256Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Sha256Hash, Sha256Hash>(hash);
    }

    #[cfg(feature = "sha3")]
    {
      let hash = Sha3Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Sha3Hash, Sha3Hash>(hash);
    }

    #[cfg(feature = "blake3")]
    {
      let hash = Blake3Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Blake3Hash, Blake3Hash>(hash);
    }
  }

  #[test]
  fn hash_prefix() {
    init_test_logger();

    //== Test Prefix Creation ==/
    let prefix = HashPrefix::new(&[0xDEu8, 0xAD][..], 12);
    assert_eq!(prefix.prefix[1], 0xA0); // Extra bits zeroed

    //== Child Prefix Extension ==//
    let child = prefix.child(5, 27).unwrap();
    dbg!(&child);
    assert_eq!(child.prefix[1], 0xAD);
    assert_eq!(child.prefix[2], 0x80);
    assert_eq!(child.prefix_len, 17);

    //== Lower and Upper Bounds ==/
    #[cfg(feature = "md5")]
    {
      let hash: Md5Hash = prefix.lower_bound();
      assert_eq!(
        hash.0,
        [
          0xde, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00
        ]
      );
      let hash: Md5Hash = prefix.upper_bound();
      assert_eq!(
        hash.0,
        [
          0xde, 0xaf, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff
        ]
      );
    }

    //== Child Index Determination ==/
    let hash = GlyphHash::new(b"hunter2");
    let prefix = HashPrefix::new(&[0x50], 4);
    let child_idx = prefix.which_child(hash.hash_bytes(), 4).unwrap();
    assert_eq!(child_idx, 5);
    let child_idx = prefix.which_child(hash.hash_bytes(), 8).unwrap();
    assert_eq!(child_idx, 93);
    let child_idx = prefix.which_child(hash.hash_bytes(), 12).unwrap();
    assert_eq!(child_idx, 1500);
  }
}
