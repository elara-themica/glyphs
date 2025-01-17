/// A macro wrapper for returning an [`Result::Err`] that allows logging of
/// errors.  
///
/// Specifically, in either debug build mode (or if the glifs-trace feature is
/// enabled), before an `Err` is returned calls are made to [`log::debug`] and
/// [`log::trace`] that describe the error and the stack backtrace,
/// respectively.
///
/// Usage:  `err!(trace: U) -> Result::Err(U)`   .
macro_rules! err {
  ($level:ident, $error:expr) => {{
    // If testing, log the error at the debug level
    let error = $error;

    #[cfg(all(debug_assertions, feature = "log"))]
    {
      ::log::$level!("{}:{}: {:?}", file!(), line!(), &error);
      if cfg!(feature = "backtrace") {
        let bt = backtrace::Backtrace::new();
        ::log::$level!("{:?}", bt);
      }
    }

    error
  }};
}

/// Function will return a [`BufferErr::Overflow`] if check fails.
#[allow(unused)]
macro_rules! check_bounds {
  ($offset:expr, $num_bytes:expr, $buf_len:expr) => {{
    let last_byte = $offset + $num_bytes;
    if last_byte > $buf_len {
      return Err($crate::zerocopy::BufferErr::Overflow {
        needed:    last_byte,
        available: $buf_len,
      });
    } else {
      last_byte
    }
  }};
}

#[allow(unused)]
macro_rules! ok_or_return {
  ($source:expr, $ret_val:expr) => {
    match $source {
      Ok(result) => result,
      Err(_) => return $ret_val,
    }
  };
}

/// Generates a zero-copy version of primitive type.
///
/// # Requirements
///
/// - The conversion between the native and zero-copy type must be the same on
///   all platforms (e.g., always little-endian).
/// - The type must have a complete ordering for collation.
///
/// # Parameters
///
/// - `native_prim`: The corresponding native primitive type (e.g., `u32`)
/// - `zc_type`: The desired name for the generated zero-copy type.
/// - `from_bytes`: An expression or function to read the native type from
///                 a byte array
/// - `to_bytes`: An expression or function to convert the native type to a
///               byte array.
/// - `cmp_fn`: An expression or function to compare two references to the
///             native type.  If the native type implements `Ord`, you can just
///             use `Ord::cmp` here.
macro_rules! gen_zc_prim {
  ($native_prim:ident,
    $zc_prim:ident,
    $from_bytes:expr,
    $to_bytes:expr,
    $cmp_fn:expr,
    $zc_type_id:ident,
    $glyph_type:ident,
    conv_usize
  ) => {
    gen_zc_prim!(
      $native_prim,
      $zc_prim,
      $from_bytes,
      $to_bytes,
      $cmp_fn,
      $zc_type_id,
      $glyph_type
    );

    impl TryFrom<usize> for $zc_prim {
      type Error = <$native_prim as TryFrom<usize>>::Error;

      fn try_from(value: usize) -> Result<Self, Self::Error> {
        Ok($zc_prim::from($native_prim::try_from(value)?))
      }
    }
  };

  ($native_prim:ident,
    $zc_prim:ident,
    $from_bytes:expr,
    $to_bytes:expr,
    $cmp_fn:expr,
    $zc_type_id:ident,
    $glyph_type:ident
  ) => {
    /// A zero-copy version of the corresponding primitive type.
    #[repr(transparent)]
    #[derive(Copy, Clone)]
    pub struct $zc_prim([u8; size_of::<$native_prim>()]);

    unsafe impl ZeroCopy for $zc_prim {}

    impl $crate::zerocopy::HasZeroCopyID for $zc_prim {
      const ZERO_COPY_ID: ZeroCopyTypeID = ZeroCopyTypeID::$zc_type_id;
    }

    impl ZeroCopyGlyph for $zc_prim {
      const GLYPH_TYPE_ID: GlyphType = GlyphType::$glyph_type;
    }

    impl $zc_prim {
      /// Creates an instance of the primitive from an array of bytes.
      ///
      /// Note that any types with endianness must be little-endian.
      pub fn from_bytes(bytes: [u8; size_of::<$native_prim>()]) -> $zc_prim {
        $zc_prim(bytes)
      }

      /// Gets the associated native primitive
      pub fn get(&self) -> $native_prim {
        ($from_bytes)(self.0)
      }

      /// Retrieves the raw bytes of the type.
      pub fn bytes(&self) -> &[u8; size_of::<$native_prim>()] {
        &self.0
      }
    }

    impl core::convert::From<$native_prim> for $zc_prim {
      fn from(src: $native_prim) -> Self {
        $zc_prim(($to_bytes)(src))
      }
    }

    impl core::convert::From<$zc_prim> for $native_prim {
      fn from(src: $zc_prim) -> Self {
        ($from_bytes)(src.0)
      }
    }

    impl core::cmp::Eq for $zc_prim {}

    impl core::cmp::PartialEq for $zc_prim {
      fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
      }
    }

    impl core::cmp::PartialEq<$native_prim> for $zc_prim {
      fn eq(&self, other: &$native_prim) -> bool {
        let a = self.get();
        $cmp_fn(&a, other).is_eq()
      }
    }

    impl core::cmp::PartialOrd for $zc_prim {
      fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
      }
    }

    impl core::cmp::Ord for $zc_prim {
      fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let a = ($from_bytes)(self.0);
        let b = ($from_bytes)(other.0);
        $cmp_fn(&a, &b)
      }
    }

    impl core::fmt::Debug for $zc_prim {
      fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let a = $native_prim::from(*self);
        core::fmt::Debug::fmt(&a, f)
      }
    }

    impl core::fmt::Display for $zc_prim {
      fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        let a = $native_prim::from(*self);
        core::fmt::Display::fmt(&a, f)
      }
    }

    impl Default for $zc_prim {
      fn default() -> Self {
        $native_prim::default().into()
      }
    }
  };
}

/// Generates a [`ToGlyph`] implementation for a primitive type.
///
/// There are three patterns that are available, depending on whether we want to
/// write a short glyph or whether we want to convert to a different [`ZeroCopy`]
/// type before writing.
///
/// - If you want to write a short glyph, use the pattern
///   `($source_type, $glyph_type, short, $conv_fn)`.
/// - If you want to write a type that needs to be converted into a zero copy
///   type first, use the pattern
///   `($source_type, $glyph_type, conv, $zc_type, $conv_fn`.
/// - Otherwise, if you are writing a type that implements `ZeroCopy`, use the
///   pattern `($source_type, $glyph_type)`.
///
/// # Parameters
///
/// - `source_type`: The type to be written into the target glyph.
/// - `glyph_type`: The variant of [`GlyphType`] for the glyph to be written.]
/// - `zc_type`: When converting the `source_type` to an intermediate zero copy
///              type, the name of that type.
/// - `conv_fn`: An expression or function that converts from the source type
///              to a `[u8; 4]` (for a short glyph) or to the mediating zero
///              copy type.
macro_rules! gen_prim_to_glyph {
  ($source_type:ident, $glyph_type:ident) => {
    impl $crate::ToGlyph for $source_type {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), GlyphErr> {
        unsafe {
          // Consolidated bounds check for writing glyph of primitive
          $crate::zerocopy::bounds_check(target, *cursor + self.glyph_len())?;
          $crate::GlyphHeader::new(
            $crate::GlyphType::$glyph_type,
            size_of::<$source_type>(),
          )
          .unwrap_unchecked()
          .bbwr_u(target, cursor);
          self.bbwr_u(target, cursor);
          Ok(())
        }
      }

      fn glyph_len(&self) -> usize {
        size_of::<$crate::GlyphHeader>() + size_of::<$source_type>()
      }
    }
  };

  ($source_type:ident, $glyph_type:ident, short, $conv_fn:expr) => {
    impl $crate::ToGlyph for $source_type {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), GlyphErr> {
        let bytes: [u8; 4] = ($conv_fn)(self);
        $crate::GlyphHeader::new_short($crate::GlyphType::$glyph_type, bytes)
          .bbwr(target, cursor)?;
        Ok(())
      }

      fn glyph_len(&self) -> usize {
        size_of::<$crate::GlyphHeader>()
      }
    }
  };

  ($source_type:ident, $glyph_type:ident, conv, $zc_type:ident, $conv_fn:expr) => {
    impl $crate::ToGlyph for $source_type {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), GlyphErr> {
        // SAFETY: We perform one bounds check for the entire vector.
        unsafe {
          $crate::zerocopy::bounds_check(target, *cursor + self.glyph_len())?;
          $crate::GlyphHeader::new(
            $crate::GlyphType::$glyph_type,
            size_of::<$zc_type>(),
          )
          .unwrap_unchecked()
          .bbwr_u(target, cursor);
          let zct: $zc_type = ($conv_fn)(self);
          zct.bbwr_u(target, cursor);
          Ok(())
        }
      }

      fn glyph_len(&self) -> usize {
        size_of::<$crate::GlyphHeader>()
          + $crate::zerocopy::round_to_word(size_of::<$zc_type>())
      }
    }
  };
}

/// Generate a [`FromGlyph`] implementation to read a type from a source glyph.
///
/// # Decoding Options
///
/// There are three different patterns for this macro that can be used,
/// depending on how the target type should be decoded.
///
/// - If the target type is [`ZeroCopy`] and should be read from the regular
///   contents of the glyph (i.e. the source type is not a short glyph), then
///   just use the pattern `($target_ty:ident, $glyph_ty:ident)`.
/// - If the target type should be read from a short glyph, then use the pattern
///   `($target_ty:ident, $glyph_ty:ident, short, $read:expr)`.
/// - If the target type must be converted from another decoded type, e.g.,
///   if a `u8` being decoded from a `u32` first, use the pattern
///   `($target_ty:ident, try_conv, $med_type:ident, $conv:expr)`.
///
/// # Parameters
///
/// - `target_ty`: The type being read.
/// - `glyph_ty`: A glyph type id from [`GlyphType`] (e.g., `U16`).
/// - `read_fn`: An expression or function that can read the target type from
///              a `[u8; 4]`.
/// - `med_type`: When doing the read through a mediating type, the (zero-copy)
///               mediating type.
/// - `conv_fn`: When doing the read through a mediating type, an expression or
///              function to attempt conversion from the mediating type into the
///              target type.
macro_rules! gen_prim_from_glyph {
  ($target_type:ident, basic) => {
    impl<G: Glyph> crate::FromGlyph<G> for $target_type {
      fn from_glyph(glyph: G) -> Result<Self, GlyphErr> {
        let result =
          $crate::basic::BasicGlyph::<G, $target_type>::from_glyph(glyph);
        let val = $crate::util::LogErr::<
          $crate::basic::BasicGlyph<G, $target_type>,
          $crate::GlyphErr,
        >::log_err(result, log::Level::Trace)?;
        Ok(*vl)
      }
    }
  };

  ($target_type:ident, try_conv_glyph, $glyph_type:ident, $conv_fn:expr) => {
    impl<G: Glyph> FromGlyph<G> for $target_type {
      fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
        let mediating = match $glyph_type::from_glyph(glyph.borrow()) {
          Ok(mediating) => mediating,
          Err(err) => {
            let (_glyph, err) = err.into_parts();
            return Err(FromGlyphErr::new(glyph, err.into()));
          },
        };
        let val = match ($conv_fn)(mediating) {
          Ok(val) => val,
          Err(err) => return Err(FromGlyphErr::new(glyph, err.into())),
        };
        Ok(val)
      }
    }
  };

  ($target_type:ident, conv_glyph, $glyph_type:ident, $conv_fn:expr) => {
    impl<G: Glyph> FromGlyph<G> for $target_type {
      fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
        let mediating = $glyph_type::<G>::from_glyph(glyph)?;
        let val = ($conv_fn)(mediating);
        Ok(val)
      }
    }
  };

  ($target_type:ident, conv, $glyph_type:ident, $conv_fn:expr) => {
    impl<G: Glyph> FromGlyph<G> for $target_type {
      fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
        let mediating = $glyph_type::from_glyph(glyph)?;
        let val = ($conv_fn)(mediating);
        Ok(val)
      }
    }
  };
}

/// Generates an implementation of [`ToGlyph`] for a slice of primitive types.
///
/// There are two patterns that are available, depending on whether the source
/// type is [`ZeroCopy`].
///
/// - If the source type is `ZeroCopy`, then use the pattern
///   `($source_type:ident, $glyph_type:ident)`
/// - Otherwise, a conversion function will be necessary for each item; use
///   `($source_type:ident, $glyph_type:ident, conv, $zc_type:ident, $conv_fn:expr)`.
///
/// # Parameters
///
/// - `source_type`: The (slice of) type to generate the `impl` for.
/// - `glyph_type`: The variant of [`GlyphType`] for the glyph to be written.
/// - `zc_type`: If the source type requires conversion, this is the zero-copy
///              type it will be converted into before writing.
/// - `conv_fn`: An expression or function that converts `source_type` into
///              `zc_type`.
macro_rules! gen_prim_slice_to_glyph {
  ($source_type:ident) => {
    impl $crate::ToGlyph for [$source_type] {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), $crate::GlyphErr> {
        unsafe {
          // Consolidated bounds check for writing glyph of primitives
          $crate::zerocopy::bounds_check(target, *cursor + self.glyph_len())?;
          let header = $crate::GlyphHeader::new(
            $crate::GlyphType::VecBasic,
            size_of::<$crate::collections::BasicVecGlyphHeader>()
              + size_of::<$crate::zerocopy::U32>()
              + size_of::<$source_type>() * self.len(),
          )?;
          header.bbwr_u(target, cursor);
          let header2 =
            crate::collections::BasicVecGlyphHeader::new::<$source_type>(1)?;
          header2.bbwr_u(target, cursor);
          let len = $crate::zerocopy::U32::try_from(self.len())?;
          len.bbwr_u(target, cursor);
          $source_type::bbwrs_u(self, target, cursor);
          $crate::zerocopy::pad_to_word_u(target, cursor);
          Ok(())
        }
      }

      fn glyph_len(&self) -> usize {
        size_of::<$crate::GlyphHeader>()
          + size_of::<$crate::collections::BasicVecGlyphHeader>()
          + size_of::<$crate::zerocopy::U32>()
          + $crate::zerocopy::round_to_word(
            size_of::<$source_type>() * self.len(),
          )
      }
    }
  };

  ($source_type:ident,conv, $zc_type:ident, $conv_fn:expr) => {
    impl $crate::ToGlyph for [$source_type] {
      fn glyph_encode(
        &self,
        target: &mut [u8],
        cursor: &mut usize,
      ) -> Result<(), GlyphErr> {
        unsafe {
          // Consolidated bounds check for writing glyph of primitives
          $crate::zerocopy::bounds_check(target, *cursor + self.glyph_len())?;
          let header = $crate::GlyphHeader::new(
            $crate::GlyphType::VecBasic,
            size_of::<$crate::collections::BasicVecGlyphHeader>()
              + size_of::<U32>()
              + size_of::<$zc_type>() * self.len(),
          )?;
          header.bbwr_u(target, cursor);
          let header2 =
            crate::collections::BasicVecGlyphHeader::new::<$zc_type>(1)?;
          header2.bbwr_u(target, cursor);
          let len = $crate::zerocopy::U32::try_from(self.len())?;
          len.bbwr_u(target, cursor);
          for element in self.iter() {
            let zct: $zc_type = ($conv_fn)(element);
            zct.bbwr_u(target, cursor);
          }
          $crate::zerocopy::pad_to_word_u(target, cursor);
          Ok(())
        }
      }

      fn glyph_len(&self) -> usize {
        size_of::<$crate::GlyphHeader>()
          + size_of::<$crate::collections::BasicVecGlyphHeader>()
          + size_of::<U32>()
          + $crate::zerocopy::round_to_word(
            size_of::<$source_type>() * self.len(),
          )
      }
    }
  };
}

/// Generate a [`FromGlyph`] implementation that converts from a [`ParsedGlyph`]
/// to a slice of zero-copy types that is parsed from the underlying buffer.
///
/// # Requirements
///
/// - The target type must implement [`ZeroCopy`].
/// - The source glyph type must be expected to contain a vector of the zero
///   copy type.
///
/// # Parameters
///
/// - `zc_type`: The target zero-copy type.
/// - `glyph_type`: A glyph type id from [`GlyphType`] (e.g., `VecU16`).
macro_rules! gen_prim_slice_from_glyph_parsed {
  ($zc_type:ty) => {
    impl<'a> $crate::FromGlyph<$crate::ParsedGlyph<'a>> for &'a [$zc_type] {
      fn from_glyph(
        glyph: $crate::ParsedGlyph<'a>,
      ) -> Result<Self, $crate::FromGlyphErr<$crate::ParsedGlyph<'a>>> {
        let bvg = $crate::collections::BasicVecGlyph::<
                                                      $crate::ParsedGlyph<'a>,
                                                    >::from_glyph(glyph)?;
        let slice = match bvg.get_parsed::<$zc_type>() {
          Ok(slice) => slice,
          Err(err) => return Err(FromGlyphErr::new(glyph, err.into())),
        };
        Ok(slice)
      }
    }
  };

  ($zc_type:ty, le_native, $native_type:ty) => {
    impl<'a> $crate::FromGlyph<$crate::ParsedGlyph<'a>> for &'a [$zc_type] {
      fn from_glyph(
        glyph: $crate::ParsedGlyph<'a>,
      ) -> Result<Self, $crate::FromGlyphErr<$crate::ParsedGlyph<'a>>> {
        let bvg = $crate::collections::BasicVecGlyph::<
                                          $crate::ParsedGlyph<'a>
                                        >::from_glyph(glyph)?;
        let slice = match bvg.get_parsed::<$zc_type>() {
          Ok(slice) => slice,
          Err(err) => return Err(FromGlyphErr::new(glyph, err.into())),
        };
        Ok(slice)
      }
    }

    #[cfg(target_endian = "little")]
    impl<'a> $crate::FromGlyph<$crate::ParsedGlyph<'a>>
      for &'a [$native_type]
    {
      fn from_glyph(
        glyph: $crate::ParsedGlyph<'a>,
      ) -> Result<Self, $crate::FromGlyphErr<$crate::ParsedGlyph<'a>>> {
        let bvg = $crate::collections::BasicVecGlyph::<
                              $crate::ParsedGlyph<'a>,
                            >::from_glyph(glyph)?;
        let as_zc_slice = match bvg.get_parsed::<$zc_type>() {
          Ok(slice) => slice,
          Err(err) => return Err(FromGlyphErr::new(glyph, err.into())),
        };
        if as_zc_slice.as_ptr().is_aligned() {
          unsafe {
            Ok(core::mem::transmute::<&'a [$zc_type], &'a [$native_type]>(
              as_zc_slice,
            ))
          }
        } else {
          Err($crate::GlyphErr::UnalignedSlice {
            needed: align_of::<$native_type>(),
            addr:   as_zc_slice.as_ptr() as usize,
          }.into_fge(glyph))
        }
      }
    }
  };
}
