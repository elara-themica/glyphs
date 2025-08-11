//! Glyph (de-)serialization for arrays, slices, and vectors, as well as the
//! dynamic [`VecGlyph`].
//!
//! The format of vector glyphs is as follows:
//! - A [`GlyphHeader`]
//! - A [`VecGlyphHeader`], which includes the number of items in the
//!   vector glyph.
//! - An array of [`U32`]s, giving the offset of each item from the start
//!   of the items buffer.  Note that this array is the official list of
//!   items--technically, multiple items could refer to the same
//!   underlying bytes if they contain the same offset.
//! - The remaining bytes of the glyph are a buffer for the glyphs it
//!   contains.
use crate::{
  crypto::{Blake3Hash, Md5Hash, Sha1Hash, Sha256Hash, Sha3Hash},
  dynamic::DynGlyph,
  glyph_close,
  zerocopy::{
    bounds_check, pad_to_word, round_to_word, BasicVecType, InBasicVec,
    ZeroCopy, F32, F64, I128, I16, I32, I64, U128, U16, U32, U64,
  },
  DecodeErr, EncodedGlyph, FromGlyph, Glyph, GlyphErr, GlyphHeader,
  GlyphOffset, GlyphSorting, GlyphType, ToGlyph,
};
use core::{
  borrow::Borrow,
  cmp::Ordering,
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
};
use std::{marker::PhantomData, ops::Deref};
use uuid::Uuid;

/// The specific type header for (non-primitive) vector glyphs.
///
/// - `format_version` must be equal to zero (experimental version)
/// - `reserved` must be equal to zero.
/// - `num_items` indicates the number of glyphs contained in the `VecGlyph`.
#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub(crate) struct VecGlyphHeader {
  num_items: U32,
}

impl VecGlyphHeader {
  /// Creates a new type-specific header for a [`VecGlyph`].
  ///
  /// As the values for `format_version` and `reserved` are fixed, only the
  /// number of glyphs present in the `VecGlyph` must be specified.
  pub fn new(num_items: usize) -> Result<VecGlyphHeader, GlyphErr> {
    let num_items = u32::try_from(num_items)
      .map_err(|_e| GlyphErr::VecGlyphLenOverflow { num_items })?;
    Ok(VecGlyphHeader {
      num_items: U32::from(num_items),
    })
  }

  /// Returns the number of items contained in the VecGlyph.
  pub fn num_items(&self) -> usize {
    self.num_items.get() as usize
  }
}

unsafe impl ZeroCopy for VecGlyphHeader {}

/// A glyph that contains a vector of other glyphs.
pub struct VecGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  /// The source glyph that is a vector glyph
  glyph: G,

  /// Pointer to the offsets table.
  offsets: NonNull<[GlyphOffset]>,
}

impl<G> VecGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  /// Returns the number of items (glyphs) in the vector.
  pub fn len(&self) -> usize {
    self.offsets().len()
  }

  /// Returns true iff the `VecGlyph` contains no items.
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the `index`-th glyph in the vector.
  pub fn get(&self, index: usize) -> Option<&Glyph> {
    let offset = self.offsets().get(index)?;
    let mut cursor = offset.cursor(0);
    match Glyph::read(self.glyph.content_padded(), &mut cursor) {
      Ok(glyph) => Some(glyph),
      Err(_) => None,
    }
  }

  /// Returns the `index`-th glyph in the vector, returning an error if the
  /// glyph does not decode correctly.
  pub fn get_checked(&self, index: usize) -> Result<Option<&Glyph>, GlyphErr> {
    if let Some(offset) = self.offsets().get(index) {
      let mut cursor = offset.cursor(0);
      let glyph = Glyph::read(self.glyph.content_padded(), &mut cursor)?;
      Ok(Some(glyph))
    } else {
      Ok(None)
    }
  }

  /// An iterator over contained glyphs.
  pub fn iter(
    &self,
  ) -> impl Iterator<Item = &Glyph> + Clone + DoubleEndedIterator + ExactSizeIterator
  {
    VecGlyphIterator {
      offsets: self.offsets(),
      content: self.glyph.content_padded(),
    }
  }

  /// Limits pointer unsafety by immediately binding lifetime to `&'_ self`.
  fn offsets(&self) -> &[GlyphOffset] {
    unsafe { self.offsets.as_ref() } // SAFETY: Guaranteed by trait bounds
  }
}

impl<'a> VecGlyph<&'a Glyph> {
  /// Returns the `index`-th glyph in the vector.
  pub fn get_parsed(&self, index: usize) -> Option<&'a Glyph> {
    let offset = self.offsets().get(index)?;
    let mut cursor = offset.cursor(0);
    match Glyph::read(self.glyph.content_padded(), &mut cursor) {
      Ok(glyph) => Some(glyph),
      Err(_) => None,
    }
  }

  /// Returns the `index`-th glyph in the vector, returning an error if the
  /// glyph does not decode correctly.
  pub fn get_checked_parsed(
    &self,
    index: usize,
  ) -> Result<Option<&'a Glyph>, GlyphErr> {
    if let Some(offset) = self.offsets().get(index) {
      let mut cursor = offset.cursor(0);
      let glyph = Glyph::read(self.glyph.content_padded(), &mut cursor)?;
      Ok(Some(glyph))
    } else {
      Ok(None)
    }
  }

  /// An iterator over contained glyphs.
  pub fn iter_parsed(&self) -> impl Iterator<Item = &'a Glyph> + Clone {
    unsafe {
      VecGlyphIterator {
        offsets: self.offsets.as_ref(),
        content: self.glyph.content_padded(),
      }
    }
  }
}

impl<G> Debug for VecGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    write!(f, "VecGlyph")?;
    let mut df = f.debug_list();
    for glyph in self.iter() {
      let dg = DynGlyph::new(glyph);
      df.entry(&dg);
    }
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for VecGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph.deref()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    let mut self_iter = self.iter().map(|g| DynGlyph::new(g));
    let mut other_iter = other.iter().map(|g| DynGlyph::new(g));

    loop {
      match (self_iter.next(), other_iter.next()) {
        (Some(a), Some(b)) => {
          let ordering = a.glyph_ord(&b, sorting); // Adjust comparison logic if needed
          if ordering != Ordering::Equal {
            return ordering;
          }
        },
        (Some(_), None) => return Ordering::Greater,
        (None, Some(_)) => return Ordering::Less,
        (None, None) => return Ordering::Equal,
      }
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for VecGlyph<G> {}

impl<G> FromGlyph<G> for VecGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(source: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Vec) {
      return Err(DecodeErr::new(source, err.into()));
    }
    let contents = source.content_padded();
    let mut cursor = 0;
    let header = match VecGlyphHeader::bbrf(contents, &mut cursor) {
      Ok(header) => header,
      Err(err) => return Err(DecodeErr::new(source, err.into())),
    };
    let offsets =
      match GlyphOffset::bbrfs(contents, &mut cursor, header.num_items()) {
        Ok(offsets) => offsets,
        Err(err) => return Err(DecodeErr::new(source, err.into())),
      };
    let offsets = NonNull::from(offsets);
    Ok(Self {
      glyph: source,
      offsets,
    })
  }
}

impl<G: Deref<Target = Glyph>> Ord for VecGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for VecGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for VecGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// An iterator through the items of a [`VecGlyph`].
#[derive(Copy, Clone)]
struct VecGlyphIterator<'a> {
  offsets: &'a [GlyphOffset],
  content: &'a [u8],
}

impl<'a> DoubleEndedIterator for VecGlyphIterator<'a> {
  fn next_back(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_last()?;
    self.offsets = remainder;
    let mut cursor = offset.cursor(0);
    Glyph::read(self.content, &mut cursor).ok()
  }
}

impl<'a> ExactSizeIterator for VecGlyphIterator<'a> {
  fn len(&self) -> usize {
    self.offsets.len()
  }
}

impl<'a> Iterator for VecGlyphIterator<'a> {
  type Item = &'a Glyph;

  fn next(&mut self) -> Option<Self::Item> {
    let (offset, remainder) = self.offsets.split_first()?;
    self.offsets = remainder;
    let mut cursor = offset.cursor(0);
    Glyph::read(self.content, &mut cursor).ok()
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.len();
    (len, Some(len))
  }
}

/// Serializes data into a vector of glyphs.
///
/// Ideally, this could be done with a blanket implementation, but until
/// specialization lands in stable rust, this would also cause basic types
/// (e.g., `Vec<u32>`) to be written as a series of individual glyphs rather
/// than as a much more efficient and convenient [`BasicVecGlyph`].
///
/// This type has constructors that accept slices, clonable iterators, and
/// types with references that implement [`IntoIterator`] (i.e., you could even
/// use it directly with an owned [`Vec`] if you wanted to).
///
/// ```rust
/// # use glyphs::collections::VecGlyphWriter;
/// # use glyphs::{Glyph, GlyphType, ToGlyph};
/// let source = vec!["a", "vec", "of", "str"];
///
/// // Until rust's `#[feature(specialization)]` is finished, this requires a
/// // blanket implementation that would frequently do the wrong thing.
/// //
/// // let glyph = Glyph::new(&source).unwrap();
///
/// // So do this, instead:
/// let writer = VecGlyphWriter::from_slice(&source[..]);
/// let glyph = Glyph::new(writer).unwrap();
/// assert_eq!(glyph.glyph_type(), GlyphType::Vec);
/// ```
///
/// This type has constructors that accept slices, clonable iterators, and
/// types with references that implement [`IntoIterator`] (i.e., you could even
/// use it directly with an owned [`Vec`] if you wanted to).
///
pub struct VecGlyphWriter<T>(T);

// We use `()` for `T` here, because the trait solver can't infer the correct
// types without it!  Hopefully this gets fixed at some point...
impl VecGlyphWriter<()> {
  /// New instance from a slice of the source type.
  ///
  /// ```rust
  /// # use glyphs::collections::VecGlyphWriter;
  /// # use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// # use glyphs::{Glyph, GlyphType, ToGlyph};
  ///
  /// // Write a slice of hashes as a series of glyphs instead of using the
  /// // standard / more efficient `BasicVecGlyph`.
  /// let source = [GlyphHash::zero(); 5];
  /// let adapter = VecGlyphWriter::from_slice(&source[..]);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::Vec);
  /// ```
  pub fn from_slice<'a, T: ToGlyph>(slice: &'a [T]) -> impl ToGlyph + 'a {
    VecGlyphWriter(ClonableIteratorAdapter(slice.iter()))
  }

  /// New instance from a clonable iterator.
  ///
  /// ```rust
  /// # use glyphs::collections::VecGlyphWriter;
  /// # use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// # use glyphs::{Glyph, GlyphType};
  ///
  /// // Write a slice of `u8`s as a series of glyphs instead of using the
  /// // standard / more efficient `BasicVecGlyph`, directly from a mapping
  /// // iterator.
  /// let source = [1u8, 2u8, 3u8];
  /// let map = (&source[..]).iter().map(|val| val + 1);
  /// let adapter = VecGlyphWriter::from_clonable_iterator(map);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::Vec);
  /// ```
  pub fn from_clonable_iterator<I>(iter: I) -> impl ToGlyph
  where
    I: Iterator + ExactSizeIterator + Clone,
    I::Item: ToGlyph,
  {
    VecGlyphWriter(ClonableIteratorAdapter(iter))
  }
}

impl<I> VecGlyphWriter<I>
where
    for<'a> &'a I: IntoIterator,
    for<'a> <&'a I as IntoIterator>::IntoIter: ExactSizeIterator,
    for<'a> <&'a I as IntoIterator>::Item: ToGlyph,
{
  /// New instance from any type that can be iterated over.
  ///
  /// Specifically, a _reference_ to the iterable must implement the
  /// [`IntoIterator`] trait.  The [`Iterator`] it produces must have a known
  /// size (i.e., implement [`ExactSizeIterator`]).
  ///
  /// While this works well with a standard [`Vec`], it notably does not work
  /// with a slice!  While a reference to a slice _is_ iterable, we need the
  /// reference to our generic type to be iterable!  We can't accept the `[T]`
  /// type as this generic because it's `!Sized` and so we can't create a new
  /// instance of the type.  Oh the other hand, we can't use a `&[T]` as that
  /// generic type either, because a reference to _that_ (i.e., `&&[T]`)
  /// doesn't implement `IntoIterator`.  Finally, we can't use the slice's
  /// iterator directly because (1) iterators are consumable, and we'll need to
  /// iterate over the items at least twice (once for length), and (2) while a
  /// reference to [`Iter`](type@core::iter::Iter) could theoretically implement
  /// `IntoIterator` because it implements [`Clone`], the standard library
  /// doesn't actually implement this trait.
  ///
  /// For slices, just use [`from_slice()`] instead.  We use an internal adapter
  /// type to get around #3, though we omit that from our public interface by
  /// returning an opaque type instead.
  ///
  /// Finally, note that using this constructor typically requires helping the
  /// trait solver by specifying the type that the resulting iterator will be
  /// producing, even though it should be trivially obvious!  (It's the exact
  /// same type as the parameter.)  Some of the error messages I got while
  /// trying to find an API shape that would work for this suggested that this
  /// is a known limitation in the trait solver, so hopefully this can be fixed
  /// at some point.
  ///
  /// ```rust
  /// use glyphs::collections::VecGlyphWriter;
  /// use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// use glyphs::{Glyph, GlyphType};
  ///
  /// let source = vec!["a", "vec", "of", "str"];
  /// // NOTE!  The turbofish operator is typically required here, even though
  /// //        the resulting type is be trivially obvious!  (It's the same type
  /// //        as the parameter)
  /// let adapter = VecGlyphWriter::<Vec<&str>>::from_iterable(source);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::Vec);
  /// ```
  pub fn from_iterable(iterable: I) -> impl ToGlyph
  {
    VecGlyphWriter(iterable)
  }
}

impl<C> ToGlyph for VecGlyphWriter<C>
where
    for<'a> &'a C: IntoIterator,
    for<'a> <&'a C as IntoIterator>::IntoIter: ExactSizeIterator,
    for<'a> <&'a C as IntoIterator>::Item: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let iter = self.0.into_iter();
    let mut vgs = VecGlyphSerializer::new(iter.len(), target, cursor)?;
    for field in iter {
      vgs.add_field(&field)?;
    }
    vgs.finish()
  }

  fn glyph_len(&self) -> usize {
    let iter = self.0.into_iter();
    let mut len_calc = VecGlyphLenCalc::new();
    for field in iter {
      len_calc.add_item(field.glyph_len());
    }
    len_calc.finish()
  }
}


#[derive(Copy, Clone, Eq, PartialOrd, PartialEq, Debug)]
#[repr(packed)]
pub(crate) struct BasicVecGlyphHeader {
  /// A type identifier.  See [`BasicVecType`].
  pub basic_type_id: U16,

  /// The number of dimensions in a multidimensional array.
  pub tensor_rank: u8,

  reserved: u8,
}

impl BasicVecGlyphHeader {
  pub(crate) fn tensor_rank(&self) -> usize {
    self.tensor_rank as usize
  }

  // FIXME: Docs
  pub fn new<T: InBasicVec>(tensor_rank: usize) -> Result<Self, GlyphErr> {
    let tensor_rank = u8::try_from(tensor_rank)
      .map_err(|_t| GlyphErr::TensorRankOverflow(tensor_rank))?;

    Ok(Self {
      basic_type_id: T::BASIC_VEC_TYPE.into(),
      tensor_rank,
      reserved: Default::default(),
    })
  }

  pub fn confirm_zero_copy_type(
    &self,
    expected: BasicVecType,
  ) -> Result<(), GlyphErr> {
    let observed = self.get_zero_copy_type_id();
    if observed == expected {
      Ok(())
    } else {
      Err(GlyphErr::UnexpectedZeroCopyType { expected, observed })
    }
  }

  pub fn get_zero_copy_type_id(&self) -> BasicVecType {
    self.basic_type_id.into()
  }
}

unsafe impl ZeroCopy for BasicVecGlyphHeader {}

/// A simple vector of a zero-copy type.
///
/// The type is generic over the type of glyph `G`, allowing it to be
/// constructed from borrowed or owned data, and over the corresponding type
/// `T`, which must implement [`ZeroCopyGlyph`].  This requires that the type
/// be readable directly from a string of bytes (i.e., is [`ZeroCopy`]) as well
/// as providing an associated [`GlyphType`].
///
/// This type can only be constructed via the [`FromGlyph`] trait, which will
/// check that (1) type ID of the source glyph matches that of the target type,
/// and (2) will perform a bounds check to ensure the glyph is large enough to
/// contain an instance of `T`.
///
/// Types with a size of <= 4 bytes will be written as short glyphs and read
/// from the glyph header.
///
pub struct BasicVecGlyph<G: Deref<Target = Glyph>> {
  glyph:          G,
  header:         NonNull<BasicVecGlyphHeader>,
  tensor_lengths: NonNull<[U32]>,
  data:           NonNull<[u8]>,
}

impl<G: Deref<Target = Glyph>> BasicVecGlyph<G> {
  /// Returns the glyph's type-specific header.
  fn header(&self) -> BasicVecGlyphHeader {
    unsafe { self.header.as_ref().clone() }
  }

  /// Returns the ZeroCopy type contained in the glyph.
  pub fn type_id(&self) -> BasicVecType {
    self.header().basic_type_id.into()
  }

  /// Returns `Err` the glyph does not contain a vector of the specified type.
  pub fn confirm_type<T: InBasicVec>(&self) -> Result<(), GlyphErr> {
    self.header().confirm_zero_copy_type(T::BASIC_VEC_TYPE)
  }

  /// Returns the array's tensor rank.
  ///
  /// A tensor's rank is the number of dimensions into which the vector is
  /// split.
  ///
  /// - A scalar is a tensor of rank 0.
  /// - A vector is a tensor of rank 1.
  /// - A matrix is a tensor of rank 2.
  /// - And so on...
  pub fn tensor_rank(&self) -> usize {
    self.header().tensor_rank as usize
  }

  /// Returns the size of each dimension of the tensor.
  pub fn dimension_lengths(&self) -> &[U32] {
    unsafe { self.tensor_lengths.as_ref() }
  }

  /// Returns the raw bytes from the vector.
  ///
  /// This is the entire contents of the glyph, minus the header and tensor
  /// dimension lengths.
  pub fn as_bytes(&self) -> &[u8] {
    unsafe { self.data.as_ref() }
  }

  /// Returns a reference to the vector of the specified type.
  ///
  /// Returns an error if the type ID of `[T]` does not match the type ID
  /// stored in the glyph.
  pub fn get<T: InBasicVec>(&self) -> Result<&[T], GlyphErr> {
    self.confirm_type::<T>()?;
    let bytes = self.as_bytes();
    let slice = T::bbrfs_i(bytes, &mut 0);
    Ok(slice)
  }
}

impl<'a> BasicVecGlyph<&'a Glyph> {
  /// Get a reference to the contained array, but with a lifetime bound by
  /// the underlying byte buffer.
  pub fn as_bytes_parsed(&self) -> &'a [u8] {
    // SAFETY: Glyph referenced is immutable, pinned, and result's lifetime is
    //         bound by that of the underlying buffer.
    unsafe { self.data.as_ref() }
  }

  /// Returns a reference to the vector of the specified type.
  ///
  /// Returns an error if the type ID of `[T]` does not match the type ID
  /// stored in the glyph.
  pub fn get_parsed<T: InBasicVec>(&self) -> Result<&'a [T], GlyphErr> {
    self.confirm_type::<T>()?;
    let bytes = self.as_bytes_parsed();
    let slice = T::bbrfs_i(bytes, &mut 0);
    Ok(slice)
  }
}

impl<G: Deref<Target = Glyph>> Debug for BasicVecGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("BasicVecGlyph");
    df.field("dimension_lengths", &self.dimension_lengths());
    df.field("type", &self.type_id());

    match self.type_id() {
      BasicVecType::U8 => {
        let values: &[u8] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::U16 => {
        let values: &[U16] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::U32 => {
        let values: &[U32] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::U64 => {
        let values: &[U64] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::U128 => {
        let values: &[U128] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::I8 => {
        let values: &[i8] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::I16 => {
        let values: &[I16] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::I32 => {
        let values: &[I32] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::I64 => {
        let values: &[I64] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::I128 => {
        let values: &[I128] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::F32 => {
        let values: &[F32] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::F64 => {
        let values: &[F64] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::HashMD5 => {
        let values: &[Md5Hash] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::HashSHA1 => {
        let values: &[Sha1Hash] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::HashSHA2 => {
        let values: &[Sha256Hash] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::HashSHA3 => {
        let values: &[Sha3Hash] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::HashBlake3 => {
        let values: &[Blake3Hash] = self.get().unwrap();
        df.field("values", &values);
      },
      BasicVecType::UUID => {
        let values: &[Uuid] = self.get().unwrap();
        df.field("values", &values);
      },
      _ => {
        df.field("type_id", &self.header().get_zero_copy_type_id());
        df.field("bytes", &self.as_bytes());
      },
    }
    df.finish()
  }
}

impl<G: Deref<Target = Glyph>> EncodedGlyph<G> for BasicVecGlyph<G> {
  fn into_inner(self) -> G {
    self.glyph
  }

  fn glyph(&self) -> &Glyph {
    &self.glyph.deref()
  }

  fn glyph_ord(&self, other: &Self, sorting: GlyphSorting) -> Ordering {
    match sorting {
      GlyphSorting::TypeAndBytes => self
        .header()
        .basic_type_id
        .get()
        .cmp(&other.header().basic_type_id.get())
        .then(self.as_bytes().cmp(other.as_bytes())),
      GlyphSorting::Experimental => match (self.type_id(), other.type_id()) {
        (BasicVecType::U8, BasicVecType::U8) => {
          let a: &[u8] = self.get().unwrap();
          let b: &[u8] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::U16, BasicVecType::U16) => {
          let a: &[U16] = self.get().unwrap();
          let b: &[U16] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::U32, BasicVecType::U32) => {
          let a: &[U32] = self.get().unwrap();
          let b: &[U32] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::U64, BasicVecType::U64) => {
          let a: &[U64] = self.get().unwrap();
          let b: &[U64] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::U128, BasicVecType::U128) => {
          let a: &[U128] = self.get().unwrap();
          let b: &[U128] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::I8, BasicVecType::I8) => {
          let a: &[i8] = self.get().unwrap();
          let b: &[i8] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::I16, BasicVecType::I16) => {
          let a: &[I16] = self.get().unwrap();
          let b: &[I16] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::I32, BasicVecType::I32) => {
          let a: &[I32] = self.get().unwrap();
          let b: &[I32] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::I64, BasicVecType::I64) => {
          let a: &[I64] = self.get().unwrap();
          let b: &[I64] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::I128, BasicVecType::I128) => {
          let a: &[I128] = self.get().unwrap();
          let b: &[I128] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::F32, BasicVecType::F32) => {
          let a: &[F32] = self.get().unwrap();
          let b: &[F32] = other.get().unwrap();
          a.partial_cmp(b).unwrap_or(Ordering::Equal)
        },
        (BasicVecType::F64, BasicVecType::F64) => {
          let a: &[F64] = self.get().unwrap();
          let b: &[F64] = other.get().unwrap();
          a.partial_cmp(b).unwrap_or(Ordering::Equal)
        },
        (BasicVecType::HashMD5, BasicVecType::HashMD5) => {
          let a: &[Md5Hash] = self.get().unwrap();
          let b: &[Md5Hash] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::HashSHA1, BasicVecType::HashSHA1) => {
          let a: &[Sha1Hash] = self.get().unwrap();
          let b: &[Sha1Hash] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::HashSHA2, BasicVecType::HashSHA2) => {
          let a: &[Sha256Hash] = self.get().unwrap();
          let b: &[Sha256Hash] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::HashSHA3, BasicVecType::HashSHA3) => {
          let a: &[Sha3Hash] = self.get().unwrap();
          let b: &[Sha3Hash] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::HashBlake3, BasicVecType::HashBlake3) => {
          let a: &[Blake3Hash] = self.get().unwrap();
          let b: &[Blake3Hash] = other.get().unwrap();
          a.cmp(b)
        },
        (BasicVecType::UUID, BasicVecType::UUID) => {
          let a: &[Uuid] = self.get().unwrap();
          let b: &[Uuid] = other.get().unwrap();
          a.cmp(b)
        },
        (_, _) => self
          .header()
          .basic_type_id
          .get()
          .cmp(&other.header().basic_type_id.get())
          .then(self.as_bytes().cmp(other.as_bytes())),
      },
    }
  }
}

impl<G: Deref<Target = Glyph>> Eq for BasicVecGlyph<G> {}

impl<G> FromGlyph<G> for BasicVecGlyph<G>
where
  G: Deref<Target = Glyph>,
{
  type Error = GlyphErr;

  fn from_glyph(glyph: G) -> Result<Self, DecodeErr<G, Self::Error>> {
    if let Err(err) = glyph.header().confirm_type(GlyphType::VecBasic) {
      return Err(DecodeErr::new(glyph, err));
    }
    let cursor = &mut 0;
    let content = glyph.content();
    let header = match BasicVecGlyphHeader::bbrf(content, cursor) {
      Ok(header) => header,
      Err(err) => return Err(DecodeErr::new(glyph, err.into())),
    };
    let tensor_lengths = match U32::bbrfs(content, cursor, header.tensor_rank())
    {
      Ok(tensor_lengths) => tensor_lengths,
      Err(err) => return Err(DecodeErr::new(glyph, err.into())),
    };
    let tensor_lengths = NonNull::from(tensor_lengths);
    *cursor = round_to_word(*cursor);
    let data = NonNull::from(u8::bbrfs_i(content, cursor));
    let header = NonNull::from(header);
    Ok(Self {
      glyph,
      header,
      tensor_lengths,
      data,
    })
  }
}

impl<G: Deref<Target = Glyph>> Ord for BasicVecGlyph<G> {
  fn cmp(&self, other: &Self) -> Ordering {
    self.glyph_ord(other, Default::default())
  }
}

impl<G: Deref<Target = Glyph>> PartialEq for BasicVecGlyph<G> {
  fn eq(&self, other: &Self) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl<G: Deref<Target = Glyph>> PartialOrd for BasicVecGlyph<G> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

/// Serializes data into a basic vector glyph.
///
/// Unlike [`VecGlyphWriter`], which serializes any data implementing
/// [`ToGlyph`] into a series of individual glyphs, i.e., a [`VecGlyph`], this
/// type serializes fixed-length, zero-copy types implementing [`InBasicVec`]
/// into a basic vector glyph containing _only_ the target type, i.e., a
/// [`BasicVecGlyph`].  After optimization, serialization should typically be
/// just a memory copy, and no de-serialization is required so long as
/// we don't require alignment greater than 8 bytes.
///
/// Many such types (e.g., `[&`[`GlyphHash`]`]`) already have implementations
/// of `ToGlyph` that use this type for serialization, but blanket
/// implementations are not currently possible due to the lack of specialization
/// in stable rust.
///
/// See the [`module level documentation`](module@crate::collections) for an
/// overview.
///
/// ```rust
/// # use glyphs::collections::BasicVecGlyphWriter;
/// # use glyphs::crypto::{CryptographicHash, GlyphHash};
/// # use glyphs::{Glyph, GlyphType};
/// let source = vec![GlyphHash::zero(); 5];
/// let adapter = BasicVecGlyphWriter::from_iterable(source);
/// let glyph = Glyph::new(adapter).unwrap();
/// assert_eq!(glyph.glyph_type(), GlyphType::VecBasic);
/// ```
pub struct BasicVecGlyphWriter<C, T>(C, PhantomData<T>);

impl<'a, C, T> BasicVecGlyphWriter<C, T>
where
  C: 'a,
  &'a C: IntoIterator,
  <&'a C as IntoIterator>::IntoIter: ExactSizeIterator,
  <&'a C as IntoIterator>::Item: Borrow<T>,
  T: InBasicVec,
{
  /// New instance from any type that can be iterated over.
  ///
  /// Specifically, a _reference_ to the iterable must implement the
  /// [`IntoIterator`] trait.  The [`Iterator`] it produces must have a known
  /// size (i.e., implement [`ExactSizeIterator`]), and the items this iterator
  /// produces must be a type from which an instance of the type to be written
  /// into the basic vector glyph can be borrowed (e.g., if `T: InBasicVec`,
  /// then the iterator could produce a `T`, `&T`, `Box<T>`, etc...).
  ///
  /// While this works well with a standard [`Vec`], it notably does not work
  /// with a slice (see source comments for details).  For slices use
  /// [`from_slice()`] instead.
  ///
  /// ```rust
  /// # use glyphs::collections::BasicVecGlyphWriter;
  /// # use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// # use glyphs::{Glyph, GlyphType};
  /// let source = [1u8, 2u8, 3u8];
  /// let adapter = BasicVecGlyphWriter::from_slice(&source[..]);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::VecBasic);
  /// ```
  pub fn from_iterable(iterable: C) -> Self {
    Self(iterable, Default::default())
  }
}

impl<I, T> BasicVecGlyphWriter<I, T>
where
  I: Iterator + ExactSizeIterator + Clone,
  I::Item: Borrow<T>,
  T: InBasicVec,
{
  /// New instance from a clonable iterator.
  ///
  /// ```rust
  /// # use glyphs::collections::BasicVecGlyphWriter;
  /// # use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// # use glyphs::{Glyph, GlyphType};
  /// let source = [1u8, 2u8, 3u8];
  /// let map = (&source[..]).iter().map(|val| val + 1);
  /// let adapter = BasicVecGlyphWriter::from_clonable_iterator(map);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::VecBasic);
  /// ```
  pub fn from_clonable_iterator(iter: I) -> impl ToGlyph {
    BasicVecGlyphWriter(ClonableIteratorAdapter(iter), Default::default())
  }
}

impl<'a, T>
BasicVecGlyphWriter<(), T>
where
  T: InBasicVec,
{
  /// New instance from a slice of [`InBasicVec`].
  ///
  /// ```rust
  /// use glyphs::collections::BasicVecGlyphWriter;
  /// use glyphs::crypto::{CryptographicHash, GlyphHash};
  /// use glyphs::{Glyph, GlyphType};
  ///
  /// let source = [1u8, 2u8, 3u8];
  /// let adapter = BasicVecGlyphWriter::from_slice(&source[..]);
  /// let glyph = Glyph::new(adapter).unwrap();
  /// assert_eq!(glyph.glyph_type(), GlyphType::VecBasic);
  /// ```
  pub fn from_slice(slice: &'a [T]) -> impl ToGlyph + 'a {
    BasicVecGlyphWriter(ClonableIteratorAdapter(slice.iter()), PhantomData::<T>)
  }
}

impl<C, T> ToGlyph for BasicVecGlyphWriter<C, T>
where
    for<'b> &'b C: IntoIterator,
    for<'b> <&'b C as IntoIterator>::IntoIter: ExactSizeIterator,
    for<'b> <&'b C as IntoIterator>::Item: Borrow<T>,
    T: InBasicVec,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    assert_glyph_alignment!(debug, *cursor);

    // Content length isn't just glyph length minus header; padding matters
    let content_len = size_of::<BasicVecGlyphHeader>()
      + size_of::<U32>()
      + size_of::<T>() * self.0.into_iter().len();
    let glyph_len = size_of::<GlyphHeader>() + round_to_word(content_len);

    // Consolidated bounds check for writing glyph of primitives
    bounds_check(target, *cursor + glyph_len)?;

    GlyphHeader::new(GlyphType::VecBasic, content_len)?.bbwr(target, cursor)?;

    // Secondary header contains type id and tensor rank
    BasicVecGlyphHeader::new::<T>(1)?.bbwr(target, cursor)?;

    // With a simple array, the length of the first tensor rank is the length
    // of the entire array. No need to pad, because of the size of the
    // secondary header and one tensor rank length, we're already at a multiple
    // of 8 bytes
    U32::try_from(self.0.into_iter().len())?.bbwr(target, cursor)?;
    assert_glyph_alignment!(debug, *cursor);

    // Write the actual data.
    for item in self.0.into_iter() {
      item.borrow().bbwr(target, cursor)?;
    }

    // Zero pad out the glyph
    pad_to_word(target, cursor)?;
    Ok(())
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<BasicVecGlyphHeader>()
      + size_of::<U32>()
      + round_to_word(size_of::<T>() * self.0.into_iter().len())
  }
}


/// Quasi-private serializer for vector glyphs--calculates glyph length.
///
/// This is marked as public for `serde-glyph`, but should not be considered
/// part of this crate's public / stable API.
#[doc(hidden)]
#[derive(Default)]
pub struct VecGlyphLenCalc {
  num_items: usize,
  items_len: usize,
}

impl VecGlyphLenCalc {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn add_item(&mut self, item_len: usize) {
    self.num_items = self.num_items.saturating_add(1);
    self.items_len = self.items_len.saturating_add(item_len);
  }

  pub fn finish(self) -> usize {
    size_of::<GlyphHeader>()
      + round_to_word(
        size_of::<VecGlyphHeader>() + size_of::<GlyphOffset>() * self.num_items,
      )
      + self.items_len
  }
}

/// Quasi-private serializer for vector glyphs.
///
/// This is marked as public for `serde-glyph`, but should not be considered
/// part of this crate's public / stable API.
#[doc(hidden)]
pub struct VecGlyphSerializer<'a> {
  target:         &'a mut [u8],
  cursor:         &'a mut usize,
  glyph_start:    usize,
  content_start:  usize,
  offsets_cursor: usize,
}

impl<'a> VecGlyphSerializer<'a> {
  pub fn new(
    len: usize,
    target: &'a mut [u8],
    cursor: &'a mut usize,
  ) -> Result<Self, GlyphErr> {
    let glyph_start = *cursor;
    *cursor += size_of::<GlyphHeader>();
    let content_start = *cursor;
    VecGlyphHeader::new(len)?.bbwr(target, cursor)?;
    let offsets_cursor = GlyphOffset::skip(target, cursor, len, true)?;
    Ok(Self {
      target,
      cursor,
      glyph_start,
      content_start,
      offsets_cursor,
    })
  }

  pub fn add_field<T: ToGlyph>(&mut self, field: &T) -> Result<(), GlyphErr> {
    GlyphOffset::new(*self.cursor - self.content_start)?
      .bbwr(self.target, &mut self.offsets_cursor)?;
    field.glyph_encode(self.target, self.cursor)
  }

  pub fn finish(self) -> Result<(), GlyphErr> {
    glyph_close(
      GlyphType::Vec,
      self.target,
      self.glyph_start,
      self.cursor,
      false,
    )?;
    Ok(())
  }
}



/// Private adapter class for [`VecGlyphWriter`] and [`BasicVecGlyphWriter`] to
/// accept more (and more convienent) user types.
struct ClonableIteratorAdapter<T>(T);

impl<'a, T> IntoIterator for &'a ClonableIteratorAdapter<T>
where
  T: Iterator + Clone,
{
  type IntoIter = T;
  type Item = T::Item;

  fn into_iter(self) -> Self::IntoIter {
    self.0.clone()
  }
}




#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn codec_glyph_vec() {
    let strings = std::vec![
      "I",
      "am",
      "the",
      "very",
      "model",
      "of",
      "a",
      "modern",
      "Major-General",
    ];
    let writer = VecGlyphWriter::from_slice(&strings[..]);
    let glyph = Glyph::new(writer).unwrap();

    let vg = VecGlyph::from_glyph(glyph).unwrap();
    for (i, glyph) in vg.iter().enumerate() {
      let dec = <&str>::from_glyph(glyph).unwrap();
      assert_eq!(dec, strings[i]);
    }

    let numbers = std::vec![0u8, 1, 2, 3, 4, 5, 6, 7];
    let bgv = Glyph::new(&numbers[..]).unwrap();
    assert_eq!(bgv.glyph_type(), GlyphType::VecBasic);
    let decoded = BasicVecGlyph::from_glyph(bgv).unwrap();
    assert_eq!(decoded.type_id(), BasicVecType::U8);
    assert_eq!(decoded.get::<u8>().unwrap(), &numbers[..]);
  }
  
}
