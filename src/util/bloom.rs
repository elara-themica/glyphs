use crate::{util::debug::ShortHexDump, GlyphErr};
use core::{
  fmt::{Debug, Formatter},
  hash::Hasher,
  iter::repeat,
};
use siphasher::sip128::SipHasher13;

/// Provides debug information on a bloom filter's size and % fill.
pub(crate) struct BloomFilterOccupancy(usize, usize);

impl BloomFilterOccupancy {
  /// Created from the raw of a bloom filter.
  pub fn new(bloom_filter: &[u8]) -> Self {
    let num_bits = bloom_filter.len() * 8;
    let mut bits_set = 0usize;
    for byte in bloom_filter {
      bits_set += byte.count_ones() as usize;
    }
    Self(bits_set, num_bits)
  }

  /// The number of 1s in the filter
  pub fn bits_set(&self) -> usize {
    self.0
  }

  /// The total # of bits in the filter
  pub fn bits_len(&self) -> usize {
    self.1
  }

  /// The proportion (`[0,1]`) of bits in the filter that are `1`.
  pub fn occupancy(&self) -> f32 {
    self.0 as f32 / self.1 as f32
  }
}

impl Debug for BloomFilterOccupancy {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "BloomFilterOccupancy({}/{} ({:.2}%))",
      self.0,
      self.1,
      self.occupancy() * 100.0
    )
  }
}

/// A Simple Bloom Filter.
///
/// A simple zero-copy bloom filter for use in glyphs.  The filter itself
/// contains the byte array (m) and the number of hash functions (k), and
/// expects types using it to define, set and check these hash functions
/// themselves.  However, functions using Sip-1-3 from the `siphasher` crate
/// are provided for convenience.  See [`Self::add_sip13()`] and
/// [`Self::check_sip13`].
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BloomFilter<T>
where
  T: AsRef<[u8]>,
{
  num_hashes: usize,
  data:       T,
}

impl<T> BloomFilter<T>
where
  T: AsRef<[u8]>,
{
  /// Creates a new bloom filter.
  pub fn new(data: T, num_hashes: usize) -> Self {
    Self { num_hashes, data }
  }

  /// The underlying byte array storing the contents of the bloom filter.
  pub fn data(&self) -> &[u8] {
    self.data.as_ref()
  }

  /// Whether the specified bit is set to 1.
  ///
  /// This function returns `None` if `bit` is outside the range stored by
  /// the bloom filter.
  pub fn get_bit(&self, bit: usize) -> Option<bool> {
    let byte = bit / 8;
    let bit = bit % 8;

    if let Some(byte) = self.data.as_ref().get(byte) {
      let mask = 1u8 << bit;
      Some((mask & byte) != 0)
    } else {
      None
    }
  }

  pub fn num_bits(&self) -> usize {
    self.data.as_ref().len() * 8
  }

  pub fn num_hashes(&self) -> usize {
    self.num_hashes
  }

  pub fn num_bits_set(&self) -> usize {
    let mut bits_set = 0usize;
    for byte in self.data.as_ref() {
      bits_set += byte.count_ones() as usize;
    }
    bits_set
  }

  pub(crate) fn occupancy(&self) -> impl Debug {
    BloomFilterOccupancy::new(self.data())
  }

  /// Returns `true` iff the bloom filter contains the specified key.
  pub fn check_sip13(&self, key: &[u8]) -> bool {
    let mut result = true; // Unless otherwise proven, key is in filter.
    let mut hasher = SipHasher13::new();
    hasher.write(key);
    let mut num_hashes = self.num_hashes;
    while num_hashes > 0 {
      let hash = hasher.finish();
      let bit = (hash % self.num_bits() as u64) as usize;
      if let Some(is_set) = self.get_bit(bit) {
        if !is_set {
          result = false;
        }
      }
      num_hashes -= 1;
      hasher = SipHasher13::new_with_keys(0, hash);
    }
    result
  }

  pub fn borrow(&self) -> BloomFilter<&[u8]> {
    let data = self.data.as_ref();
    BloomFilter {
      num_hashes: self.num_hashes,
      data,
    }
  }
}

impl<T> BloomFilter<T>
where
  T: AsRef<[u8]> + AsMut<[u8]>,
{
  /// Mutable access the underlying bloom filter data.
  pub fn data_mut(&mut self) -> &mut [u8] {
    self.data.as_mut()
  }

  /// Set the specified bit to `1`.
  ///
  /// If the bit is outside the range of this bloom filter, this function has
  /// no effect.
  fn set_bit(&mut self, bit: usize) {
    let byte = bit / 8;
    let bit = bit % 8;

    if let Some(byte) = self.data.as_mut().get_mut(byte) {
      let mask = 1u8 << bit;
      *byte |= mask;
    }
  }

  /// Add the given key to the bloom filter.
  pub fn add_sip13(&mut self, key: &[u8]) {
    let mut hasher = SipHasher13::new();
    hasher.write(key);
    let mut num_hashes = self.num_hashes;
    while num_hashes > 0 {
      let hash = hasher.finish();
      let bit = (hash % self.num_bits() as u64) as usize;
      self.set_bit(bit);
      num_hashes -= 1;
      hasher = SipHasher13::new_with_keys(0, hash);
    }
  }
}

impl<T> AsRef<[u8]> for BloomFilter<T>
where
  T: AsRef<[u8]>,
{
  fn as_ref(&self) -> &[u8] {
    self.data.as_ref()
  }
}

impl BloomFilter<alloc::boxed::Box<[u8]>> {
  /// Calculate the optimum bloom filter size and number of hash functions based
  /// on the expected occupancy and target false positive rate.
  ///
  /// Bloom filter parameters:
  ///
  /// - `n`: the number of items in the bloom filter.
  /// - `p`: the target rate of false positives.
  /// - `m`: the number of bytes in the bloom filter.
  /// - `k`: the number of hash functions calculated for each item.
  ///
  /// The arguments to this function are the parameters `n` and `k`, as described
  /// above.  The function returns (`m`, `k`), where `m` is rounded up to the
  /// nearest multiple of 256 bits and `k` is rounded to nearest whole number.
  pub fn new_optimum(
    n: usize,
    p: f64,
  ) -> Result<BloomFilter<alloc::boxed::Box<[u8]>>, GlyphErr> {
    let n = n as f64; // for subsequent math
    let m = -(n * p.log(core::f64::consts::E))
      / 2.0f64.log(core::f64::consts::E).powf(2.0f64);
    let m = m.ceil() as usize + 255 & !255;

    let k = -p.log(core::f64::consts::E) / 2.0f64.log(core::f64::consts::E);
    let k = k.round() as usize;

    // SAFETY: Just zero init a new box of [u8].  Why does this even require unsafe?
    let buffer: alloc::boxed::Box<[u8]> = repeat(0).take(m / 8).collect();

    Ok(Self {
      num_hashes: k,
      data:       buffer,
    })
  }
}

impl<T> Debug for BloomFilter<T>
where
  T: AsRef<[u8]>,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("BloomFilter");
    df.field("num_hashes", &self.num_hashes());
    df.field("num_bits", &self.num_bits());
    df.field("num_bits_set", &self.num_bits_set());
    df.field("data", &ShortHexDump(self.data(), 0));
    df.finish()
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn bloom() {
    let mut bytes = [0u8; 32];

    let mut bloom = BloomFilter::new(&mut bytes[..], 1);
    for i in 0..bloom.num_bits() {
      assert_eq!(bloom.get_bit(i), Some(false));
      bloom.set_bit(i);
      assert_eq!(bloom.get_bit(i), Some(true));
    }

    let mut bloom = BloomFilter::new_optimum(200, 0.01).unwrap();

    for i in 0u64..200 {
      bloom.add_sip13(&(i * 2).to_le_bytes()[..]);
    }

    for i in 0u64..200 {
      assert_eq!(bloom.check_sip13(&(i * 2).to_le_bytes()[..]), true);
    }

    let mut n_fp = 0;
    for i in 0u64..200 {
      if bloom.check_sip13(&(i * 2 + 1).to_le_bytes()[..]) {
        n_fp += 1;
      }
    }
    std::dbg!(n_fp);
    assert!(n_fp < 5);
  }
}
