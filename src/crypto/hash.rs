//! Contains the GLIFS-internal interface to cryptographic hashing functions.
//!
//! Note that GLIFS itself does not contain any cryptographic code, but does
//! have its own internal API to those functions in anticipation of using
//! implementations from different places (e.g., where OpenSSL may not always
//! be available)

use crate::{
  glyph::{Glyph, GlyphType},
  util::debug::ShortHexDump,
  zerocopy::{HasZeroCopyID, ZeroCopy, ZeroCopyTypeID, U16},
  FromGlyph, GlyphErr, ParsedGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  marker::PhantomData,
  mem::{size_of, transmute},
};

// TODO: Test implementing these from another crate, and fully convert trait
//       call reference style to
macro_rules! hash_impls {
  ($hash_name:ident, $hash_len:expr, $hash_tid:ident, $zc_tid:ident, $context_name:ident) => {
    unsafe impl $crate::zerocopy::ZeroCopy for $hash_name {}

    impl $crate::zerocopy::HasZeroCopyID for $hash_name {
      const ZERO_COPY_ID: $crate::zerocopy::ZeroCopyTypeID =
        $crate::zerocopy::ZeroCopyTypeID::$zc_tid;
    }

    impl $crate::crypto::CryptographicHash for $hash_name {
      type Context = $context_name;

      const HASH_LEN: usize = $hash_len;
      const HASH_TYPE_ID: $crate::crypto::CryptographicHashTypeID =
        $crate::crypto::CryptographicHashTypeID::$hash_tid;
      const ZERO: Self = Self([0u8; $hash_len]);

      fn from_hash_bytes(hash_bytes: [u8; $hash_len]) -> Self {
        $hash_name(hash_bytes)
      }

      fn hash_bytes(&self) -> &[u8; $hash_len] {
        &self.0
      }
    }

    /// The default value is all zeroes.
    impl core::default::Default for $hash_name {
      fn default() -> Self {
        Self::ZERO
      }
    }

    impl core::convert::AsRef<[u8]> for $hash_name {
      fn as_ref(&self) -> &[u8] {
        &self.0[..]
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
        let glyph_header = $crate::GlyphHeader::new(
          $crate::GlyphType::HashGlyph,
          core::mem::size_of::<$crate::crypto::CryptographicHashHeader>()
            + core::mem::size_of::<$hash_name>(),
        )?;
        $crate::zerocopy::ZeroCopy::bbwr(&glyph_header, target, cursor)?;
        let hash_header = $crate::crypto::CryptographicHashHeader::new(
          $crate::crypto::CryptographicHashTypeID::$hash_tid,
        );
        $crate::zerocopy::ZeroCopy::bbwr(&hash_header, target, cursor)?;
        $crate::zerocopy::ZeroCopy::bbwr(self, target, cursor)?;
        $crate::zerocopy::pad_to_word(target, cursor)?;
        Ok(())
      }

      fn glyph_len(&self) -> usize {
        core::mem::size_of::<$crate::GlyphHeader>()
          + core::mem::size_of::<$crate::crypto::CryptographicHashHeader>()
          + $crate::zerocopy::round_to_word(core::mem::size_of::<$hash_name>())
      }
    }

    impl<G: $crate::Glyph> $crate::FromGlyph<G> for $hash_name {
      fn from_glyph(glyph: G) -> Result<Self, $crate::GlyphErr> {
        let hg = $crate::crypto::HashGlyph::<_, $hash_name>::from_glyph(glyph)?;
        let first =
          (*hg).get(0).ok_or($crate::GlyphErr::CryptoHashOverflow {
            expected: 1usize,
            observed: hg.len(),
          })?;
        Ok(*first)
      }
    }

    impl $crate::ToGlyph for [$hash_name] {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), $crate::GlyphErr> {
        let glyph_header = $crate::GlyphHeader::new(
          $crate::GlyphType::HashGlyph,
          core::mem::size_of::<$crate::crypto::CryptographicHashHeader>()
            + core::mem::size_of::<$hash_name>() * self.len(),
        )?;
        $crate::zerocopy::ZeroCopy::bbwr(&glyph_header, target, cursor)?;
        let hash_header =
          CryptographicHashHeader::new(CryptographicHashTypeID::$hash_tid);
        hash_header.bbwr(target, cursor)?;
        $hash_name::bbwrs(self, target, cursor)?;
        $crate::zerocopy::pad_to_word(target, cursor)?;
        Ok(())
      }

      fn glyph_len(&self) -> usize {
        core::mem::size_of::<$crate::GlyphHeader>()
          + core::mem::size_of::<$crate::crypto::CryptographicHashHeader>()
          + crate::zerocopy::round_to_word(size_of::<$hash_name>() * self.len())
      }
    }

    impl<'a> $crate::FromGlyph<$crate::ParsedGlyph<'a>> for &'a [$hash_name] {
      fn from_glyph(
        glyph: $crate::ParsedGlyph<'a>,
      ) -> Result<Self, $crate::GlyphErr> {
        let hg = $crate::crypto::HashGlyph::<_, $hash_name>::from_glyph(glyph)?;
        Ok($crate::crypto::HashGlyph::get_parsed(&hg))
      }
    }
  };
}

pub type GlyphHash = blake3::Blake3Hash;
pub type GlyphHashContext = blake3::Blake3Context;

#[repr(packed)]
#[derive(Copy, Clone)]
pub struct CryptographicHashHeader {
  hash_type: U16,
  reserved:  [u8; 6],
}

impl CryptographicHashHeader {
  pub fn new(hash_type: CryptographicHashTypeID) -> Self {
    Self {
      hash_type: hash_type.into(),
      reserved:  Default::default(),
    }
  }

  pub fn hash_type(&self) -> CryptographicHashTypeID {
    CryptographicHashTypeID::from(self.hash_type)
  }

  pub fn confirm_hash_type(
    &self,
    hash_type: CryptographicHashTypeID,
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

unsafe impl ZeroCopy for CryptographicHashHeader {}

#[repr(u16)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum CryptographicHashTypeID {
  MD5,
  SHA1,
  SHA2,
  SHA3,
  Blake3,

  // This must always be the last member.
  Unknown,
}

impl From<u16> for CryptographicHashTypeID {
  fn from(value: u16) -> Self {
    // SAFETY: target is #[repr(u16)]
    unsafe { core::mem::transmute::<u16, CryptographicHashTypeID>(value) }
  }
}

impl From<U16> for CryptographicHashTypeID {
  fn from(value: U16) -> Self {
    Self::from(value.get())
  }
}

impl From<CryptographicHashTypeID> for U16 {
  fn from(value: CryptographicHashTypeID) -> Self {
    U16::from(value as u16)
  }
}

pub trait CryptographicHash:
  ZeroCopy + Default + AsRef<[u8]> + Send + Sync
{
  const HASH_LEN: usize;

  /// The glyph hash type ID associated with this type of cryptographic hash.
  ///
  /// See [`CryptographicHashTypeID`].
  const HASH_TYPE_ID: CryptographicHashTypeID;

  const ZERO: Self;

  type Context: HashContext<Output = Self>;

  fn new<B: AsRef<[u8]> + ?Sized>(bytes: &B) -> Self {
    let mut context = <Self as CryptographicHash>::Context::new();
    context.update(bytes.as_ref());
    context.finish()
  }

  fn hash_bytes(&self) -> &[u8; <Self as CryptographicHash>::HASH_LEN];

  fn from_hash_bytes(
    hash_bytes: [u8; <Self as CryptographicHash>::HASH_LEN],
  ) -> Self;

  #[cfg(feature = "rand")]
  fn random<R: rand::RngCore>(rng: &mut R) -> Self
  where
    [(); <Self as CryptographicHash>::HASH_LEN]:,
  {
    let mut hash_bytes = [0u8; <Self as CryptographicHash>::HASH_LEN];
    rng.fill_bytes(&mut hash_bytes[..]);
    <Self as CryptographicHash>::from_hash_bytes(hash_bytes)
  }
}

/// Glyph containing one or more cryptographic hashes.
pub struct HashGlyph<G: Glyph, H: CryptographicHash>(G, PhantomData<H>);

impl<'a, H: CryptographicHash> HashGlyph<ParsedGlyph<'a>, H> {
  pub(crate) fn get_parsed(&self) -> &'a [H] {
    let content = self.0.content_parsed();
    let cursor = &mut 0;
    *cursor += size_of::<CryptographicHashHeader>();
    H::bbrfs_i(content, cursor)
  }
}

impl<G: Glyph, H: CryptographicHash> HashGlyph<G, H> {}

impl<G: Glyph, H: CryptographicHash> FromGlyph<G> for HashGlyph<G, H> {
  fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::HashGlyph)?;
    let content = glyph.content();
    let cursor = &mut 0;
    CryptographicHashHeader::bbrf(content, cursor)?
      .confirm_hash_type(H::HASH_TYPE_ID)?;
    Ok(Self(glyph, Default::default()))
  }
}

impl<G: Glyph, H: CryptographicHash> std::ops::Deref for HashGlyph<G, H> {
  type Target = [H];

  fn deref(&self) -> &Self::Target {
    let content = self.0.content();
    let cursor = &mut 0;
    *cursor += core::mem::size_of::<CryptographicHashHeader>();
    H::bbrfs_i(content, cursor)
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
  pub fn new(prefix_bytes: &[u8], prefix_len: usize) -> Self {
    let prefix_len = prefix_len.min(120);
    let prefix_mask = (!(u128::MAX >> prefix_len)).to_be_bytes();
    let mut prefix = [0u8; 15];
    for (dst, (src, mask)) in prefix
      .iter_mut()
      .zip(prefix_bytes.iter().zip(prefix_mask.iter()))
    {
      *dst = *src & *mask;
    }
    Self {
      prefix,
      prefix_len: prefix_len as u8,
    }
  }

  fn as_u128(&self) -> u128 {
    unsafe { u128::from_be_bytes(*transmute::<&Self, &[u8; 16]>(self)) & !0xff }
  }

  pub fn prefix_len(&self) -> usize {
    self.prefix_len as usize
  }

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
  where
    [(); H::HASH_LEN]:,
  {
    let mut buf = [0u8; H::HASH_LEN];
    for (prefix, buf) in self.prefix.iter().zip(buf.iter_mut()) {
      *buf = *prefix;
    }
    H::from_hash_bytes(buf)
  }

  /// Returns the upper bounds of the hash prefix, like a CIDR broadcast
  /// address.
  ///
  /// - Any bits after `self.length()` will be set to one.
  /// - Unlike [`Self::lower_bound()`], we cannot return a reference because the
  ///   internal storage is a fixed-length CIDR-like format.
  // TODO: Test and better docs
  pub fn upper_bound<H: CryptographicHash>(self) -> H
  where
    [(); H::HASH_LEN]:,
  {
    let prefix = self.as_u128();
    let prefix_mask = u128::MAX << 128 - self.prefix_len() as u128;
    let n_mask = !prefix_mask;
    let upper = prefix | n_mask;
    let upper = upper.to_be_bytes();

    let mut buf = [0u8; H::HASH_LEN];
    for (src, dst) in upper.iter().zip(buf.iter_mut()) {
      *dst = *src;
    }
    H::from_hash_bytes(buf)
  }

  /// The number of bits in the prefix.
  pub fn length(&self) -> usize {
    self.prefix_len as usize
  }
}

/// SAFETY: Byte arrays are inherently zero copy.
unsafe impl ZeroCopy for HashPrefix {}

impl HasZeroCopyID for HashPrefix {
  const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::HashPrefix;
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

pub(crate) mod sha2 {
  use super::*;
  #[rustfmt::skip]
  use ::sha2::Digest;

  /// The length of a SHA-2 256 byte hash value, in bytes (=32)
  pub const SHA2_256_DIGEST_BYTES: usize = 32;

  /// A SHA-2 256-bit hash value
  #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
  #[repr(packed)]
  pub struct Sha2Hash(pub [u8; SHA2_256_DIGEST_BYTES]);

  /// A context for calculating a SHA-2 256-bit hash
  #[cfg(feature = "sha2")]
  pub struct Sha2Context(::sha2::Sha256);

  #[cfg(feature = "sha2")]
  impl HashContext for Sha2Context {
    type Output = Sha2Hash;

    fn new() -> Self {
      Sha2Context(::sha2::Sha256::new())
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
      Sha2Hash(hash_bytes)
    }
  }

  hash_impls!(Sha2Hash, SHA2_256_DIGEST_BYTES, SHA2, HashSHA2, Sha2Context);
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
      blake3::Blake3Hash, md5::Md5Hash, sha1::Sha1Hash, sha2::Sha2Hash,
      sha3::Sha3Hash,
    },
    util::{init_test_logger, simple_codec_slice_test, simple_codec_test},
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
      let hash = Sha2Hash::random(&mut rng);
      simple_codec_test(hash);
      simple_codec_slice_test::<3, Sha2Hash, Sha2Hash>(hash);
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

  #[cfg(all(feature = "md5", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_md5(b: &mut Bencher) -> Result<(), GlyphErr> {
    let bytes = [0u8; 8192];

    b.bytes = bytes.len() as u64;
    b.iter(|| Md5Hash::new(&bytes[..]));

    Ok(())
  }

  #[cfg(all(feature = "sha1", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_sha1(b: &mut Bencher) -> Result<(), GlyphErr> {
    let bytes = [42u8; 8192];

    b.bytes = bytes.len() as u64;
    b.iter(|| {
      let _hash = Sha1Hash::new(&bytes[..]);
    });
    Ok(())
  }

  #[cfg(all(feature = "sha2", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_sha2(b: &mut Bencher) -> Result<(), GlyphErr> {
    let bytes = [42u8; 8192];

    b.bytes = bytes.len() as u64;
    b.iter(|| {
      let _hash = Sha2Hash::new(&bytes[..]);
    });
    Ok(())
  }

  #[cfg(all(feature = "sha3", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_sha3(b: &mut Bencher) -> Result<(), GlyphErr> {
    let bytes = [42u8; 8192];

    b.bytes = bytes.len() as u64;
    b.iter(|| {
      let _hash = Sha3Hash::new(&bytes[..]);
    });
    Ok(())
  }

  #[cfg(all(feature = "blake3", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_blake3(b: &mut Bencher) -> Result<(), GlyphErr> {
    let bytes = [42u8; 8192];

    b.bytes = bytes.len() as u64;
    b.iter(|| {
      let _hash = Blake3Hash::new(&bytes[..]);
    });
    Ok(())
  }

  // This is a deliberately slow password hash
  #[cfg(all(feature = "rust-argon2", feature = "bench_extended"))]
  #[bench]
  fn bench_hash_argon2(b: &mut Bencher) -> Result<(), GlyphErr> {
    let pw = b"hunter2";
    let pw_hash = Blake3Hash::new(pw);

    b.iter(|| {
      ::argon2::hash_raw(pw, pw_hash.as_ref(), &::argon2::Config::default())
        .unwrap()
    });

    Ok(())
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