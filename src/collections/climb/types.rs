use crate::{
  util::BloomFilter,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, I64, U16},
  GlyphErr,
};
use alloc::string::String;
use core::{cmp::Ordering, fmt::Debug, mem::transmute, str::from_utf8};

/// Types for data that may be stored in CLiMB Trees.

/// Mapping of integer type IDs to named types
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u16)]
pub enum CLiMBTreeTypeID {
  Nothing = 0x0000,
  Counter = 0x0001,
  Blake3Hash = 0x0002,
  String = 0x0003,
  Glyph = 0x0004,
  U64 = 0x0005,
  I64 = 0x0006,
  Unknown = 0x0007,
}

impl From<CLiMBTreeTypeID> for U16 {
  fn from(value: CLiMBTreeTypeID) -> Self {
    U16::from(value as u16)
  }
}

impl From<U16> for CLiMBTreeTypeID {
  fn from(value: U16) -> Self {
    if value.get() >= CLiMBTreeTypeID::Unknown as u16 {
      CLiMBTreeTypeID::Unknown
    } else {
      unsafe { transmute::<u16, CLiMBTreeTypeID>(value.get()) }
    }
  }
}

/// Types that can be used as values in a CLiMB tree.
pub trait CLiMBTreeValue:
  Clone + Debug + Send + Sized + Send + Sync + 'static
{
  /// A zero-copy reference to either this type or its serialized data.
  type RefType<'a>: Copy + Clone + Debug + Send + 'a;

  /// If the type is stored in a fixed length, that length must be stored here.
  ///
  /// In many cases, this will be equal to `Some(size_of::<Self>())`
  const FIXED_LEN: Option<usize>;

  /// If the type is reducible (e.g., reference counts) this must be
  /// set to `true`.
  ///
  /// This constant has an effect on e.g., tree query behavior.
  const REDUCE: bool;

  /// The identifier for this type in [`CLiMBTreeNode`]s.
  const TYPE_ID: CLiMBTreeTypeID;

  /// Clone a new instance from a reference.
  fn clone_from_ref(source: Self::RefType<'_>) -> Self;

  /// Produces a new (perhaps complex) reference to the type.
  ///
  /// As CLiMB Trees do not require that all types contained within are
  /// [`ZeroCopy`], references to them cannot necessarily be expressed with a
  /// `&T`.  For example, the proper reference to a `String` as written in a
  /// node is a `&str`, not a `&String`.
  fn as_ref(&self) -> Self::RefType<'_>;

  #[allow(unused_variables)]
  fn length(src: Self::RefType<'_>) -> usize {
    Self::FIXED_LEN.unwrap() // Should compile to a const...
  }

  fn read<'a>(
    source: &'a [u8],
    cursor: &mut usize,
  ) -> Result<Self::RefType<'a>, GlyphErr>;

  fn write(
    source: Self::RefType<'_>,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>;

  /// Reduce two entries with the same key.
  ///
  /// Note that this reduction always produces a new value.  This is because
  /// (1) we never expect it to be correct to discard the new value and (2) if
  /// the new value is always used this should be done by setting the associated
  /// constant `Self::REDUCE`to `false`.
  ///
  /// - This should only be called if `Self::REDUCE` is true, and we need to do
  ///   something other than simply use the newest value.
  #[allow(unused_variables)]
  fn reduce(
    older: Self::RefType<'_>,
    newer: Self::RefType<'_>,
  ) -> Option<Self> {
    unimplemented!("Type reduces but no reduce function is implemented")
  }
}

/// Types that can be used as keys in a CLiMB Tree.
///
///
pub trait CLiMBTreeKey: CLiMBTreeValue {
  /// Add the key to the provided bloom filter.
  ///
  /// After the appropriate bits are set in this function, a subsequent call
  /// to [`Self::bloom_check()`] must return `true`.
  ///
  /// Parmeters:
  ///
  /// - `key`: the source key is given as its reference type, to facilitate
  ///          zero-copy.
  /// - `bloom`: the raw bloom filter.  Implementors should assume this bloom
  ///            filter already has bits set from other keys, and must take care
  ///            not to reset any bits already set (never set bytes directly,
  ///            use a binary OR)
  /// - `num_hashes`:  The number of hashes that should be calculated and added
  ///                  to the bloom filter.  (This often will have been
  ///                  determined by calling `BloomFilter::new_optimum()`)
  fn bloom_add<T>(key: Self::RefType<'_>, bloom: &mut BloomFilter<T>)
  where
    T: AsRef<[u8]> + AsMut<[u8]>;

  /// Return false iff the key is definitely not present in the bloom filter.
  fn bloom_check(
    key: Self::RefType<'_>,
    bloom: &BloomFilter<impl AsRef<[u8]>>,
  ) -> bool;

  fn climb_tree_ord<'a>(a: Self::RefType<'a>, b: Self::RefType<'a>)
    -> Ordering;
}

impl CLiMBTreeValue for () {
  type RefType<'a> = ();

  const FIXED_LEN: Option<usize> = Some(0);
  const REDUCE: bool = false;
  const TYPE_ID: CLiMBTreeTypeID = CLiMBTreeTypeID::Nothing;

  fn clone_from_ref(_source: Self::RefType<'_>) -> Self {
    ()
  }

  fn as_ref(&self) -> Self::RefType<'_> {
    ()
  }

  fn read<'a>(
    _source: &'a [u8],
    _cursor: &mut usize,
  ) -> Result<Self::RefType<'a>, GlyphErr> {
    Ok(())
  }

  fn write(
    _source: Self::RefType<'_>,
    _target: &mut [u8],
    _cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    Ok(())
  }
}

impl CLiMBTreeValue for I64 {
  type RefType<'a> = &'a I64;

  const FIXED_LEN: Option<usize> = Some(core::mem::size_of::<I64>());
  const REDUCE: bool = false;
  const TYPE_ID: CLiMBTreeTypeID = CLiMBTreeTypeID::I64;

  fn clone_from_ref(source: Self::RefType<'_>) -> Self {
    *source
  }

  fn as_ref(&self) -> Self::RefType<'_> {
    self
  }

  fn read<'a>(
    source: &'a [u8],
    cursor: &mut usize,
  ) -> Result<Self::RefType<'a>, GlyphErr> {
    Ok(I64::bbrf(source, cursor)?)
  }

  fn write(
    source: Self::RefType<'_>,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    Ok(source.bbwr(target, cursor)?)
  }
}

impl CLiMBTreeKey for I64 {
  fn bloom_add<T>(key: Self::RefType<'_>, bloom: &mut BloomFilter<T>)
  where
    T: AsRef<[u8]> + AsMut<[u8]>,
  {
    bloom.add_sip13(key.bytes());
  }

  fn bloom_check(
    key: Self::RefType<'_>,
    bloom: &BloomFilter<impl AsRef<[u8]>>,
  ) -> bool {
    bloom.check_sip13(key.bytes())
  }

  fn climb_tree_ord<'a>(
    a: Self::RefType<'a>,
    b: Self::RefType<'a>,
  ) -> Ordering {
    a.cmp(b)
  }
}

impl CLiMBTreeValue for String {
  type RefType<'a> = &'a str;

  const FIXED_LEN: Option<usize> = None;
  const REDUCE: bool = false;
  const TYPE_ID: CLiMBTreeTypeID = CLiMBTreeTypeID::String;

  fn clone_from_ref(source: Self::RefType<'_>) -> Self {
    Self::from(source)
  }

  fn as_ref(&self) -> Self::RefType<'_> {
    AsRef::as_ref(self)
  }

  fn read<'a>(
    source: &'a [u8],
    cursor: &mut usize,
  ) -> Result<Self::RefType<'a>, GlyphErr> {
    let length = U16::bbrf(source, cursor)?;
    let bytes = u8::bbrfs(source, cursor, length.get() as usize)?;
    *cursor = round_to_word(*cursor);
    let value = from_utf8(bytes)?;
    Ok(value)
  }

  fn write(
    source: Self::RefType<'_>,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let length = u16::try_from(source.len())
      .map_err(|_| GlyphErr::ShortStringOverflow(source.len()))?;
    let length = U16::from(length);
    length.bbwr(target, cursor)?;
    u8::bbwrs(source.as_bytes(), target, cursor)?;
    pad_to_word(target, cursor)?;
    Ok(())
  }

  fn length(src: Self::RefType<'_>) -> usize {
    let length =
      round_to_word(core::mem::size_of::<U16>() + src.as_bytes().len());
    length
  }
}

impl CLiMBTreeKey for String {
  fn bloom_add<T>(key: Self::RefType<'_>, bloom: &mut BloomFilter<T>)
  where
    T: AsRef<[u8]> + AsMut<[u8]>,
  {
    bloom.add_sip13(key.as_bytes());
  }

  fn bloom_check(
    key: Self::RefType<'_>,
    bloom: &BloomFilter<impl AsRef<[u8]>>,
  ) -> bool {
    bloom.check_sip13(key.as_bytes())
  }

  fn climb_tree_ord<'a>(
    a: Self::RefType<'a>,
    b: Self::RefType<'a>,
  ) -> Ordering {
    a.cmp(b)
  }
}
