//! Types for static determination of whether vectors, slices, and arrays are
//! in sorted order.

use alloc::vec::Vec;
use core::{borrow::Borrow, ops::Deref};

pub struct SortedErr;

pub trait SortedSlice {
  type Target: Ord;

  fn sorted_slice(&self) -> &[Self::Target];
}

pub struct SortedArray<const N: usize, T>([T; N])
where
  T: Ord;

impl<const N: usize, T> SortedArray<N, T>
where
  T: Ord,
{
  /// Assumes the values are sorted.
  pub unsafe fn assume_ordered(values: [T; N]) -> Self {
    // Note that, while this function doesn't perform any unsafe operations,
    // it is marked as unsafe because other unsafe code may rely on the contents
    // being ordered.
    Self(values)
  }
}

impl<const N: usize, T> SortedSlice for SortedArray<N, T>
where
  T: Ord,
{
  type Target = T;

  fn sorted_slice(&self) -> &[T] {
    &self.0[..]
  }
}

impl<const N: usize, T> Deref for SortedArray<N, T>
where
  T: Ord,
{
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    &self.0[..]
  }
}

impl<const N: usize, T> AsRef<[T]> for SortedArray<N, T>
where
  T: Ord,
{
  fn as_ref(&self) -> &[T] {
    &self.0[..]
  }
}

impl<const N: usize, T> Borrow<[T]> for SortedArray<N, T>
where
  T: Ord,
{
  fn borrow(&self) -> &[T] {
    &self.0[..]
  }
}

impl<const N: usize, T> From<[T; N]> for SortedArray<N, T>
where
  T: Ord,
{
  fn from(mut values: [T; N]) -> Self {
    values.sort();
    Self(values)
  }
}

impl<const N: usize, T> Into<[T; N]> for SortedArray<N, T>
where
  T: Ord,
{
  fn into(self) -> [T; N] {
    self.0
  }
}

pub struct SortedSliceRef<'a, T>(&'a [T])
where
  T: Ord;

impl<'a, T> SortedSliceRef<'a, T>
where
  T: Ord,
{
  /// Assumes the values are sorted.
  pub unsafe fn assume_ordered(values: &'a [T]) -> Self {
    // Note that, while this function doesn't perform any unsafe operations,
    // it is marked as unsafe because other unsafe code may rely on the contents
    // being ordered.
    Self(values)
  }
}

impl<'a, T> SortedSlice for SortedSliceRef<'a, T>
where
  T: Ord,
{
  type Target = T;

  fn sorted_slice(&self) -> &[T] {
    self.0
  }
}

impl<'a, T> Deref for SortedSliceRef<'a, T>
where
  T: Ord,
{
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    self.0
  }
}

impl<'a, T> AsRef<[T]> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn as_ref(&self) -> &[T] {
    self.0
  }
}

impl<'a, T> Borrow<[T]> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn borrow(&self) -> &[T] {
    self.0
  }
}

impl<'a, T> TryFrom<&'a [T]> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  type Error = SortedErr;

  fn try_from(values: &'a [T]) -> Result<Self, Self::Error> {
    if values.is_sorted() {
      Ok(Self(values))
    } else {
      Err(SortedErr)
    }
  }
}

impl<'a, T> From<&'a mut [T]> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn from(values: &'a mut [T]) -> Self {
    values.sort();
    Self(values)
  }
}

impl<'a, T> From<&'a T> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn from(src: &'a T) -> Self {
    Self(core::slice::from_ref(src))
  }
}

impl<'a, T> Into<&'a [T]> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn into(self) -> &'a [T] {
    self.0
  }
}

impl<'a, T> From<&'a Option<T>> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn from(src: &'a Option<T>) -> Self {
    if let Some(thing) = src.as_ref() {
      Self(core::slice::from_ref(thing))
    } else {
      Self(&[])
    }
  }
}

impl<'a, T> From<()> for SortedSliceRef<'a, T>
where
  T: Ord,
{
  fn from(_src: ()) -> Self {
    Self(&[])
  }
}

#[cfg(feature = "alloc")]
pub struct SortedVec<T>(alloc::vec::Vec<T>)
where
  T: Ord;

#[cfg(feature = "alloc")]
impl<T> SortedVec<T>
where
  T: Ord,
{
  /// Assumes the values are sorted.
  pub unsafe fn assume_ordered(values: alloc::vec::Vec<T>) -> Self {
    // Note that, while this function doesn't perform any unsafe operations,
    // it is marked as unsafe because other unsafe code may rely on the contents
    // being ordered.
    Self(values)
  }
}

#[cfg(feature = "alloc")]
impl<T> SortedSlice for SortedVec<T>
where
  T: Ord,
{
  type Target = T;

  fn sorted_slice(&self) -> &[T] {
    &self.0[..]
  }
}

#[cfg(feature = "alloc")]
impl<T> Deref for SortedVec<T>
where
  T: Ord,
{
  type Target = [T];

  fn deref(&self) -> &Self::Target {
    &self.0[..]
  }
}

#[cfg(feature = "alloc")]
impl<'a, T> AsRef<[T]> for SortedVec<T>
where
  T: Ord,
{
  fn as_ref(&self) -> &[T] {
    &self.0[..]
  }
}

#[cfg(feature = "alloc")]
impl<'a, T> Borrow<[T]> for SortedVec<T>
where
  T: Ord,
{
  fn borrow(&self) -> &[T] {
    &self.0[..]
  }
}

#[cfg(feature = "alloc")]
impl<T> From<alloc::vec::Vec<T>> for SortedVec<T>
where
  T: Ord,
{
  fn from(mut values: alloc::vec::Vec<T>) -> Self {
    values.sort();
    Self(values)
  }
}

#[cfg(feature = "alloc")]
impl<T> Into<alloc::vec::Vec<T>> for SortedVec<T>
where
  T: Ord,
{
  fn into(self) -> Vec<T> {
    self.0
  }
}
