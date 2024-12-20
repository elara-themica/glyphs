//! Types to facilitate direct zero-copy use of data in glyphs.
//!
//! # Zero Copy Types
//!
//! Many of the basic types here are auto-generated versions of the typical
//! primitives.  The difference is that they are (1) always explicitly
//! little-endian on all platforms, and (2) not guaranteed to be aligned.
//!
//! In practice, the endian conversion will be optimized to a no-op on modern
//! platforms (x86_64, arm, etc...) because they are little-endian themselves,
//! and alignment of up to 8 bytes is typically preserved for most types in
//! glyphs.
//!
//! The main type of interest here is [`ZeroCopy`], which is an `unsafe` trait
//! that marks a type as safe to write to or read from a byte buffer directly.
//! Most importantly, this means that the type must accept any bit pattern
//! without causing undefined behavior, have a consistent binary
//! representation across all platforms (i.e., is usually little-endian), and
//! not require any specific alignment.  In practice, however, types with
//! an alignment of 8 bytes or fewer can have their alignment maintained within
//! glyphs, though it is up to the specific binary format of the specific glyph
//! type to maintain this alignment.
//!
//! There are a number of functions to facilitate reading, and, more importantly,
//! direct referencing of these types.  Here's a primer for the function names:
//!
//! - `bb*`. All functions start with `bb`; think "byte buffer".
//! - `*rd*`. Reads data into a new instance
//! - `*rf*`. References an instance of the type in place (zero-copy).
//! - `*wr*`. Writes the type into a byte buffer.
//! - `*s*`. Reads, writes, or references a _slice_ of the type, e.g., `&[U64]`.
//! - `*a*`. Reads, writes or references an _array_ of the type, e.g., a `[u8; 32]`
//! - `*_u`. An `unsafe` version that omits bounds checking.
//! - `*_i`. Reads the rest of the buffer as a slice, with the slice's length
//!          determined from the buffer's length.
//! - `*_mut*`. Creates mutable references into the buffer.
//!
//! # Utility Types
//!
//!
//! The other things of note are the enum [`ZeroCopyTypeID`], which is used by
//! some types that store these types directly without a glyph header, such as
//! vectors of [`U32`]s in a [`BasicVecGlyph`].  There is also a corresponding
//! trait [`HasZeroCopyID`] that maps these types with an ID so we can use them
//! with otherwise generic code.  There's also a [`ZeroCopyGlyph`] trait for
//! those types which have a regular glyph type associated with them as well.
//! See the documentation for [`BasicGlyph`] for more details.
use crate::{
  crypto::{CryptographicHash, GlyphHash},
  util::{collate_f32, collate_f64, MemoizedInvariant},
  GlyphErr, GlyphType,
};
use alloc::alloc::Global;
use core::{
  alloc::{AllocError, Allocator, Layout},
  cell::UnsafeCell,
  fmt::Debug,
  hint::unreachable_unchecked,
  intrinsics::{copy_nonoverlapping, transmute},
  mem::MaybeUninit,
  ptr::{write_unaligned, NonNull},
  slice::{from_raw_parts, from_raw_parts_mut},
};

#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug)]
pub struct GlyphAlloc;

#[cfg(feature = "alloc")]
unsafe impl Allocator for GlyphAlloc {
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    Global.allocate(layout.align_to(8).unwrap())
  }

  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    Global.deallocate(ptr, layout.align_to(8).unwrap())
  }
}

/// Bounds check that returns [`BufferErr`] on failure.
#[inline(always)]
pub(crate) fn bounds_check<T>(buffer: &T, to: usize) -> Result<(), GlyphErr>
where
  T: AsRef<[u8]> + ?Sized,
{
  if to > buffer.as_ref().len() {
    let err = GlyphErr::OutOfBounds {
      index:  to,
      length: buffer.as_ref().len(),
    };
    Err(err!(trace, err))
  } else {
    Ok(())
  }
}

#[inline(always)]
pub(crate) fn round_to_word(n: usize) -> usize {
  (n + 7) & !7
}

#[inline(always)]
pub(crate) fn pad_to_word(
  buffer: &mut [u8],
  cursor: &mut usize,
) -> Result<(), GlyphErr> {
  let idx_to_word = round_to_word(*cursor);
  bounds_check(buffer, idx_to_word)?;
  unsafe { pad_to_word_u(buffer, cursor) }
  Ok(())
}

#[inline(always)]
pub(crate) unsafe fn pad_to_word_u(target: &mut [u8], cursor: &mut usize) {
  let idx_to_word = (*cursor + 7) & !7;
  let bytes_remaining = idx_to_word - *cursor;
  match bytes_remaining {
    0 => {},
    1 => 0u8.bbwr_u(target, cursor),
    2 => U16::from(0).bbwr_u(target, cursor),
    3 => {
      0u8.bbwr_u(target, cursor);
      U16::from(0).bbwr_u(target, cursor);
    },
    4 => U32::from(0).bbwr_u(target, cursor),
    5 => {
      U32::from(0).bbwr_u(target, cursor);
      0u8.bbwr_u(target, cursor);
    },
    6 => {
      U32::from(0).bbwr_u(target, cursor);
      U16::from(0).bbwr_u(target, cursor);
    },
    7 => {
      U32::from(0).bbwr_u(target, cursor);
      U16::from(0).bbwr_u(target, cursor);
      0u8.bbwr_u(target, cursor);
    },
    _ => unreachable_unchecked(),
  }
}

/// [`ZeroCopy`] types with a corresponding glyph.
pub trait HasZeroCopyID: ZeroCopy {
  /// The ID used when labeling zero copy types in other glyphs.
  ///
  /// This value is used when working with these types, such as with
  /// [`BasicVecGlyph`].
  const ZERO_COPY_ID: ZeroCopyTypeID;
}

/// [`ZeroCopy`] types with a corresponding glyph.
pub trait ZeroCopyGlyph: ZeroCopy {
  /// The [`GlyphType`] used when a zero-copy type is written as a glyph.
  ///
  /// E.g., [`U64`] has a glyph type of [`GlyphType::UnsignedInt`].
  const GLYPH_TYPE_ID: GlyphType;
}

/// Indicates a type can be written directly from memory as a series of bytes.
///
/// This typically includes numeric types and other types that are
///
/* TODO: Write documentation about:
        - likely use of `gen_prim_slice_to_glyph()` and `gen_prim_slice_from_glyph_parsed()` macros
        - possible use of `gen_prim_to_glyph()` and `gen_prim_from_glyph()` macros if
          also making this type a `ZeroCopyGlyph`.

*/
pub unsafe trait ZeroCopy: Copy + Clone + Send + Sync {
  /// Reads a copy of `Self` from `source[cursor]`.
  #[inline(always)]
  fn bbrd<T>(source: &T, cursor: &mut usize) -> Result<Self, GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + size_of::<Self>())?;
    unsafe { Ok(Self::bbrd_u(source, cursor)) }
  }

  /// Reads a copy of `Self` from `source[cursor]`, with no bounds check.
  #[inline(always)]
  unsafe fn bbrd_u<T>(source: &T, cursor: &mut usize) -> Self
  where
    T: AsRef<[u8]> + ?Sized,
  {
    let ptr = source.as_ref().as_ptr().add(*cursor) as *const Self;
    *cursor += size_of::<Self>();
    *ptr
  }

  /// Copies a `[Self]` of length `items` from `source[cursor]` into a newly
  /// allocated `Vec`.
  #[inline(always)]
  #[cfg(feature = "alloc")]
  fn bbrds<T>(
    source: &T,
    cursor: &mut usize,
    items: usize,
  ) -> Result<alloc::vec::Vec<Self>, GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + size_of::<Self>() * items)?;
    unsafe { Ok(Self::bbrds_u(source, cursor, items)) }
  }

  /// Reads the rest of the buffer into a new vector.
  ///
  /// If the number of bytes remaining in the buffer is not an even multiple of
  /// the size of the objects being read, the extra bytes will be ignored.
  #[inline(always)]
  #[cfg(feature = "alloc")]
  fn bbrds_i<T>(
    source: &T,
    cursor: &mut usize,
  ) -> Result<alloc::vec::Vec<Self>, GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor)?;
    let items = (source.as_ref().len() - *cursor) / size_of::<Self>();
    unsafe { Ok(Self::bbrds_u(source, cursor, items)) }
  }

  /// An unsafe version of [`ZeroCopy::bbrds()`] without the bounds check.
  #[inline(always)]
  #[cfg(feature = "alloc")]
  unsafe fn bbrds_u<T>(
    source: &T,
    cursor: &mut usize,
    items: usize,
  ) -> alloc::vec::Vec<Self>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    let as_ref = Self::bbrfs_u(source, cursor, items);
    alloc::vec::Vec::from(as_ref)
  }

  /// Read an array of `[T; N]`.
  fn bbrda<T, const N: usize>(
    source: &T,
    cursor: &mut usize,
  ) -> Result<[Self; N], GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + size_of::<Self>() * N)?;
    unsafe { Ok(Self::bbrda_u(source, cursor)) }
  }

  /// An unsafe version of [`ZeroCopy::bbrda()`] without the bounds check.
  #[inline(always)]
  unsafe fn bbrda_u<T, const N: usize>(
    source: &T,
    cursor: &mut usize,
  ) -> [Self; N]
  where
    T: AsRef<[u8]> + ?Sized,
  {
    // SAFETY: Thanks to the restrictive bounds on `SafelyReadable`, we
    //         can just do a memcpy.
    let src_ptr = source.as_ref().as_ptr().add(*cursor);
    let src_ptr = src_ptr as *const [Self; N];
    *cursor += size_of::<Self>() * N;
    *src_ptr
  }

  /// Returns a zero-copy reference to an object at `source[cursor]`.
  #[inline(always)]
  fn bbrf<'a, T>(
    source: &'a T,
    cursor: &mut usize,
  ) -> Result<&'a Self, GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + size_of::<Self>())?;
    unsafe { Ok(Self::bbrf_u(source, cursor)) }
  }

  /// An unsafe version of [`ZeroCopy::bbrf()`] without the bounds check.
  #[inline(always)]
  unsafe fn bbrf_u<'a, T>(source: &'a T, cursor: &mut usize) -> &'a Self
  where
    T: AsRef<[u8]> + ?Sized,
  {
    let ptr = source.as_ref().as_ptr().add(*cursor) as *const Self;
    *cursor += size_of::<Self>();
    &*ptr
  }

  /// Returns a zero-copy reference to a slice of objects starting at
  /// `source[cursor]`.
  fn bbrfs<'a, T>(
    source: &'a T,
    cursor: &mut usize,
    len: usize,
  ) -> Result<&'a [Self], GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, size_of::<Self>() * len)?;
    unsafe {
      let ptr = source.as_ref().as_ptr().add(*cursor) as *const Self;
      *cursor += len * size_of::<Self>();
      Ok(from_raw_parts(ptr, len))
    }
  }

  /// An unsafe version of [`ZeroCopy::bbrfs`] without the bounds check.
  unsafe fn bbrfs_u<'a, T>(
    source: &'a T,
    cursor: &mut usize,
    len: usize,
  ) -> &'a [Self]
  where
    T: AsRef<[u8]> + ?Sized,
  {
    let ptr = source.as_ref().as_ptr().add(*cursor) as *const Self;
    *cursor += size_of::<Self>() * len;
    from_raw_parts(ptr, len)
  }

  /// References an array of `[T; N]`.
  fn bbrfa<'a, T, const N: usize>(
    source: &'a T,
    cursor: &mut usize,
  ) -> Result<&'a [Self; N], GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + N * size_of::<Self>())?;
    Ok(unsafe { Self::bbrfa_u::<T, N>(source, cursor) })
  }

  /// An unsafe version of [`ZeroCopy::bbrfa()`] without the bounds check.
  unsafe fn bbrfa_u<'a, T, const N: usize>(
    source: &'a T,
    cursor: &mut usize,
  ) -> &'a [Self; N]
  where
    T: AsRef<[u8]> + ?Sized,
  {
    // SAFETY: Thanks to the restrictive bounds on `SafelyReadable`, we
    //         can just use pointers directly
    let ptr = source.as_ref().as_ptr().add(*cursor);
    let ptr = core::mem::transmute::<*const u8, *const [Self; N]>(ptr);
    *cursor += N * size_of::<Self>();
    &*ptr
  }

  /// Copy an array of `T` into an existing target array directly from bytes in
  /// `source`.
  fn bbcps<T>(
    source: &T,
    cursor: &mut usize,
    target: &mut [Self],
  ) -> Result<(), GlyphErr>
  where
    T: AsRef<[u8]> + ?Sized,
  {
    bounds_check(source, *cursor + size_of::<Self>() * target.len())?;
    unsafe { Ok(Self::bbcps_u(source, cursor, target)) }
  }

  /// The same as [`ZeroCopy::bbcps()`], but without the bounds check.
  unsafe fn bbcps_u<T>(source: &T, cursor: &mut usize, target: &mut [Self])
  where
    T: AsRef<[u8]> + ?Sized,
  {
    // Because `Self` is `ZeroCopy`, we can just a a `memcpy`.
    // Byte copy into `target`.
    let src = source.as_ref().as_ptr().add(*cursor) as *const u8;
    let dst = target.as_ptr() as *mut u8;
    let bytes = target.len() * size_of::<Self>();
    copy_nonoverlapping(src, dst, bytes);
    *cursor += bytes;
  }

  /// Returns a reference to a slice of objects starting at `source[cursor]`
  /// through the end of `source`.
  ///
  /// Note that if the number of bytes in `source[cursor..]` is not a multiple
  /// of the size of the object being referenced, the remaining bytes will not
  /// be read, and `cursor` will point to the first ignored byte.
  #[inline(always)]
  fn bbrfs_i<'a, T>(source: &'a T, cursor: &mut usize) -> &'a [Self]
  where
    T: AsRef<[u8]> + ?Sized,
  {
    // Bounds check for starting cursor
    if *cursor > source.as_ref().len() {
      &[]
    } else {
      let items =
        source.as_ref().len().saturating_sub(*cursor) / size_of::<Self>();
      unsafe {
        let ptr = source.as_ref().as_ptr().add(*cursor) as *const Self;
        *cursor += size_of::<Self>() * items;
        from_raw_parts(ptr, items)
      }
    }
  }

  /// Write a copy of the object at `buffer[offset]`
  #[inline(always)]
  fn bbwr<T>(&self, target: &mut T, cursor: &mut usize) -> Result<(), GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
  {
    bounds_check(target, *cursor + size_of::<Self>())?;
    unsafe { Ok(Self::bbwr_u(self, target, cursor)) }
  }

  /// Write a copy of the object at `buffer[offset]`, without bounds checking.
  #[inline(always)]
  unsafe fn bbwr_u<T>(&self, target: &mut T, cursor: &mut usize)
  where
    T: AsMut<[u8]> + ?Sized,
  {
    let dst_ptr = target.as_mut().as_ptr().add(*cursor) as *mut Self;
    write_unaligned::<Self>(dst_ptr, *self);
    *cursor += size_of::<Self>()
  }

  /// Write copies a slice of objects to `buffer[offset]`, returns offset in
  /// `target` after bytes written.
  #[inline(always)]
  fn bbwrs<T>(
    source: &[Self],
    target: &mut T,
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
    Self: Sized,
  {
    bounds_check(target, *cursor + size_of::<Self>() * source.len())?;
    unsafe { Ok(Self::bbwrs_u(source, target, cursor)) }
  }

  /// Write copies a slice of objects to `buffer[offset]`, skipping bounds
  /// checking.
  #[inline(always)]
  unsafe fn bbwrs_u<T>(source: &[Self], target: &mut T, cursor: &mut usize)
  where
    T: AsMut<[u8]> + ?Sized,
    Self: Sized,
  {
    let bytes = size_of::<Self>() * source.len();
    if cfg!(target_endian = "little") {
      let src = transmute::<*const Self, *const u8>(source.as_ptr());
      let dst = target.as_mut().as_mut_ptr().add(*cursor);
      copy_nonoverlapping(src, dst, bytes);
    } else {
      let mut dst = target.as_mut().as_mut_ptr().add(*cursor) as *mut Self;
      for item in source {
        dst.write_unaligned(*item);
        dst = dst.add(1);
      }
    }
    *cursor += bytes
  }

  /// Writes copies of a slice of objects to `target[offset]`, taken from a
  /// slice of references to those objects.
  #[inline(always)]
  fn bbwrsr<T>(
    source: &[&Self],
    target: &mut T,
    cursor: &mut usize,
  ) -> Result<(), GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
  {
    bounds_check(target, *cursor + size_of::<Self>() * source.len())?;
    unsafe { Ok(Self::bbwrsr_u(source, target, cursor)) }
  }

  /// An unsafe version of [`Self::bbwrsr`], skipping bounds checks.
  #[inline(always)]
  unsafe fn bbwrsr_u<T>(source: &[&Self], target: &mut T, cursor: &mut usize)
  where
    T: AsMut<[u8]> + ?Sized,
  {
    for item in source.iter() {
      let dst = target.as_mut().as_mut_ptr().add(*cursor) as *mut Self;
      write_unaligned(dst, **item);
      *cursor += size_of::<Self>();
    }
  }

  /// Returns a zero-copy mutable reference to an object at `source[cursor]`.
  ///
  /// Note that this only works for types that are also [`ZeroCopy`].
  #[inline(always)]
  fn bbrf_mut<'a, T>(
    source: &'a mut T,
    cursor: &mut usize,
  ) -> Result<&'a mut Self, GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
    Self: ZeroCopy,
  {
    bounds_check(source, *cursor + size_of::<Self>())?;
    unsafe {
      let val = ZeroCopy::bbrf_mut_u(source, cursor);
      *cursor += size_of::<Self>();
      Ok(val)
    }
  }

  /// An unsafe version of `bbrf_mut()` skipping bounds checks.
  #[inline(always)]
  unsafe fn bbrf_mut_u<'a, T>(
    source: &'a mut T,
    cursor: &mut usize,
  ) -> &'a mut Self
  where
    T: AsMut<[u8]> + ?Sized,
    Self: ZeroCopy,
  {
    let ptr = source.as_mut().as_mut_ptr().add(*cursor) as *mut Self;
    *cursor += size_of::<Self>();
    &mut *ptr
  }

  /// Returns a zero-copy mutable reference to a slice of objects.
  ///
  /// Note that this only works for types that are also [`ZeroCopy`].
  #[inline(always)]
  fn bbrfs_mut<'a, T>(
    source: &'a mut T,
    cursor: &mut usize,
    len: usize,
  ) -> Result<&'a mut [Self], GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
    Self: ZeroCopy,
  {
    bounds_check(source, *cursor + size_of::<Self>() * len)?;
    unsafe {
      let slice = ZeroCopy::bbrfs_mut_u(source, cursor, len);
      Ok(slice)
    }
  }

  /// An unsafe version of `bbrfs_mut()` without the bounds checks.
  #[inline(always)]
  unsafe fn bbrfs_mut_u<'a, T>(
    source: &'a mut T,
    cursor: &mut usize,
    len: usize,
  ) -> &'a mut [Self]
  where
    T: AsMut<[u8]> + ?Sized,
    Self: ZeroCopy,
  {
    let ptr = source.as_mut().as_mut_ptr().add(*cursor) as *mut Self;
    *cursor += size_of::<Self>() * len;
    from_raw_parts_mut(ptr, len)
  }

  /// Returns a zero-copy mutable reference to a slice of objects, with length
  /// inferred from the remaining length of the source buffer.
  ///
  /// Note that this only works for types that are also [`ZeroCopy`].
  #[inline(always)]
  fn bbrfs_mut_i<'a, T>(source: &'a mut T, cursor: &mut usize) -> &'a mut [Self]
  where
    T: AsMut<[u8]> + ?Sized,
    Self: ZeroCopy,
  {
    // Bounds check for starting cursor
    if *cursor > source.as_mut().len() {
      &mut []
    } else {
      unsafe {
        let items =
          source.as_mut().len().saturating_sub(*cursor) / size_of::<Self>();
        let ptr = source.as_mut().as_mut_ptr().add(*cursor) as *mut Self;
        from_raw_parts_mut(ptr, items)
      }
    }
  }

  /// Mutably references an array of `[T; N]`.
  fn bbrfa_mut<'a, T, const N: usize>(
    source: &'a mut T,
    cursor: &mut usize,
  ) -> Result<&'a mut [Self; N], GlyphErr>
  where
    T: AsMut<[u8]> + AsRef<[u8]> + ?Sized,
    Self: Sized,
  {
    bounds_check(source, *cursor + N * size_of::<Self>())?;
    Ok(unsafe { Self::bbrfa_mut_u::<T, N>(source, cursor) })
  }

  /// A unsafe version of [`ZeroCopy::bbrfa_mut()`] without the bounds check.
  unsafe fn bbrfa_mut_u<'a, T, const N: usize>(
    source: &'a mut T,
    cursor: &mut usize,
  ) -> &'a mut [Self; N]
  where
    T: AsMut<[u8]> + ?Sized,
    Self: Sized,
  {
    // SAFETY: Thanks to the restrictive bounds on `SafelyReadable`, we
    //         can just use pointers directly
    let ptr = source.as_mut().as_mut_ptr().add(*cursor);
    let ptr = core::mem::transmute::<*mut u8, *mut [Self; N]>(ptr);
    *cursor = (*cursor).saturating_add(size_of::<Self>().saturating_mul(N));
    &mut *ptr
  }
}

/// An identifier specifying a basic type.
///
/// Basic types must be of fixed length and will typically be [`ZeroCopy`].
#[allow(missing_docs)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u16)]
pub enum ZeroCopyTypeID {
  U8 = 0x0000,
  U16 = 0x0001,
  U32 = 0x0002,
  U64 = 0x0003,
  U128 = 0x0004,
  U256 = 0x0005,
  U512 = 0x0006,
  I8 = 0x0007,
  I16 = 0x0008,
  I32 = 0x0009,
  I64 = 0x000A,
  I128 = 0x000B,
  I256 = 0x000C,
  I512 = 0x000D,
  F8 = 0x000E,
  F16 = 0x000F,
  F32 = 0x0010,
  F64 = 0x0011,
  F128 = 0x0012,
  F256 = 0x0013,
  F512 = 0x0014,
  HashPrefix = 0x0015,
  HashMD5 = 0x0016,
  HashSHA1 = 0x0017,
  HashSHA2 = 0x0018,
  HashSHA3 = 0x0019,
  HashBlake3 = 0x0020,
  UUID = 0x0021,
  BasicVecGlyphHeader = 0x0022,
  GlyphHeader = 0x0023,
  GlyphOffset = 0x0024,
  Unknown = 0x0025,
}

impl From<ZeroCopyTypeID> for U16 {
  fn from(value: ZeroCopyTypeID) -> Self {
    U16::from(value as u16)
  }
}

impl From<u16> for ZeroCopyTypeID {
  fn from(value: u16) -> Self {
    unsafe { transmute::<u16, ZeroCopyTypeID>(value) }
  }
}

impl From<U16> for ZeroCopyTypeID {
  fn from(value: U16) -> Self {
    unsafe { transmute::<u16, ZeroCopyTypeID>(value.get()) }
  }
}

unsafe impl ZeroCopy for u8 {}

impl HasZeroCopyID for u8 {
  const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::U8;
}

unsafe impl ZeroCopy for i8 {}

impl HasZeroCopyID for i8 {
  const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::I8;
}

gen_zc_prim!(
  u16,
  U16,
  u16::from_le_bytes,
  u16::to_le_bytes,
  Ord::cmp,
  U16,
  UnsignedInt,
  conv_usize
);
gen_zc_prim!(
  u32,
  U32,
  u32::from_le_bytes,
  u32::to_le_bytes,
  Ord::cmp,
  U32,
  UnsignedInt,
  conv_usize
);
gen_zc_prim!(
  u64,
  U64,
  u64::from_le_bytes,
  u64::to_le_bytes,
  Ord::cmp,
  U64,
  UnsignedInt,
  conv_usize
);
gen_zc_prim!(
  u128,
  U128,
  u128::from_le_bytes,
  u128::to_le_bytes,
  Ord::cmp,
  U128,
  UnsignedInt,
  conv_usize
);
gen_zc_prim!(
  i16,
  I16,
  i16::from_le_bytes,
  i16::to_le_bytes,
  Ord::cmp,
  I16,
  SignedInt,
  conv_usize
);
gen_zc_prim!(
  i32,
  I32,
  i32::from_le_bytes,
  i32::to_le_bytes,
  Ord::cmp,
  I32,
  SignedInt,
  conv_usize
);
gen_zc_prim!(
  i64,
  I64,
  i64::from_le_bytes,
  i64::to_le_bytes,
  Ord::cmp,
  I64,
  SignedInt,
  conv_usize
);
gen_zc_prim!(
  i128,
  I128,
  i128::from_le_bytes,
  i128::to_le_bytes,
  Ord::cmp,
  I128,
  SignedInt,
  conv_usize
);
gen_zc_prim!(
  f32,
  F32,
  f32::from_le_bytes,
  f32::to_le_bytes,
  collate_f32,
  F32,
  Float
);
gen_zc_prim!(
  f64,
  F64,
  f64::from_le_bytes,
  f64::to_le_bytes,
  collate_f64,
  F64,
  Float
);

/// An atomic reference-counted pointer to a byte buffer containing a glyph.
///
/// T is a state parameter, either `ArcGlyphBufUninit` or `ArcGlyphBufFinalized`, where only the
/// former allows writing.  This allows the type system to enforce the restriction that the buffer
/// is immutable once finalized and contains a valid glyph.
pub struct ArcGlyphBuf<T>(alloc::sync::Arc<UnsafeCell<[u8]>, GlyphAlloc>, T);

unsafe impl<T> Send for ArcGlyphBuf<T> {}
unsafe impl Sync for ArcGlyphBuf<ArcGlyphBufFinalized> {}

#[derive(Clone, Default)]
struct ArcGlyphHeader {
  glyph_hash: MemoizedInvariant<GlyphHash>,
}

pub struct ArcGlyphBufUninit;
pub struct ArcGlyphBufFinalized;

impl ArcGlyphBuf<ArcGlyphBufUninit> {
  pub fn new(length: usize) -> Result<Self, GlyphErr> {
    unsafe {
      // TODO: There's no try version?  There is in Box, is this an oversight by std?
      let arc = alloc::sync::Arc::<[u8], GlyphAlloc>::new_uninit_slice_in(
        size_of::<ArcGlyphHeader>() + length,
        GlyphAlloc,
      )
      .assume_init();
      let buf = Self(transmute::<_, _>(arc), ArcGlyphBufUninit);
      let ptr = (&*(buf.0.get())).get_unchecked(0) as *const u8;
      let header_ptr = transmute::<_, *mut MaybeUninit<ArcGlyphHeader>>(ptr);
      header_ptr.as_mut().unwrap().write(Default::default());
      Ok(buf)
    }
  }

  pub fn finalize(self) -> ArcGlyphBuf<ArcGlyphBufFinalized> {
    ArcGlyphBuf(self.0, ArcGlyphBufFinalized)
  }
}

impl ArcGlyphBuf<ArcGlyphBufFinalized> {
  fn header(&self) -> &ArcGlyphHeader {
    unsafe {
      let ptr = (&*(self.0.get())).get_unchecked(0) as *const u8;
      transmute::<_, _>(ptr)
    }
  }

  pub fn glyph_hash(&self) -> &GlyphHash {
    self
      .header()
      .glyph_hash
      .get(|| GlyphHash::new(self.as_ref()))
  }

  pub fn inner(&self) -> &alloc::sync::Arc<[u8], GlyphAlloc> {
    unsafe { transmute::<_, _>(&self.0) }
  }
}

impl<T> AsRef<[u8]> for ArcGlyphBuf<T> {
  fn as_ref(&self) -> &[u8] {
    unsafe {
      let ptr = self.0.get();
      &(*ptr)[size_of::<ArcGlyphHeader>()..]
    }
  }
}

impl AsMut<[u8]> for ArcGlyphBuf<ArcGlyphBufUninit> {
  fn as_mut(&mut self) -> &mut [u8] {
    // SAFETY: We've controlled this Arc from its birth, we know we have the
    //         only copy of it.  OK, OK, I know this is "never OK" but is it
    //         really?  We know there aren't any other copies of the Arc, so
    //         there should be zero risk of simultaneous access.
    //
    //         - We can't construct it any other way than with new(),
    //         - We only give it out with into_inner(), which takes an owned
    //           self and so this function wouldn't get called on it again.
    unsafe {
      let inner = transmute::<
        _,
        &mut alloc::sync::Arc<UnsafeCell<[u8]>, GlyphAlloc>,
      >(&mut self.0);
      let ptr = inner.get();
      &mut (*ptr)[size_of::<ArcGlyphHeader>()..]
    }
  }
}

impl Clone for ArcGlyphBuf<ArcGlyphBufFinalized> {
  fn clone(&self) -> Self {
    Self(self.0.clone(), ArcGlyphBufFinalized)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::dbg;

  #[test]
  fn arc_glyph() {
    dbg!(size_of::<ArcGlyphHeader>());
    assert_eq!(size_of::<ArcGlyphHeader>() % 8, 0);
    assert!(align_of::<ArcGlyphHeader>() <= 8);
  }
}
