//! Semi-structured zero-copy types used in the GLIFS data management system.
//!
//! # Overview
//!
//! The _glyphs_ data format is a semi-structured zero copy data format,
//! designed for use in large distributed systems.  Its name is inspired by the
//! human language term of the same name, which represents a unit of writing,
//! e.g., a letter.  Similarly, the data format uses the term (and type)
//! [`Glyph`] to represent a unit of meaning for a computer data management
//! system.
//!
//! - __Semi-Structured__.  The _glyphs_ data format is what's known
//!   as [semi-structuerd](https://en.wikipedia.org/wiki/Semi-structured_data).
//!   What this means is that it does not have a rigidly defined structure
//!   (like a row in a relational database table) but instead has metadata
//!   that describes its various elements and their types.  The most common
//!   example of this type of data as of this writing is a JSON object, though
//!   the two share little else in common.
//! - __Zero Copy__.  It is also a binary format, designed to be used by
//!   machines directly _without deserialization_.  Because deserialization
//!   overhead in data-intensive applications accounts for a significant
//!   proportion of all CPU use, a zero copy format can be dramatically more
//!   efficient in some cases.
//! - __Immutable__.  Once written, glyphs are intended to be immutable, as they
//!   will frequently be referred to (either directly or through a container) by
//!   a stable cryptographic hash.  Mutability takes place at higher layers,
//!   e.g., with a [document](https://en.wikipedia.org/wiki/Document-oriented_database#Documents)
//!   and different versions of [copy on write](https://en.wikipedia.org/wiki/Copy-on-write)
//!   indexes.
//!
//! # The Glyph
//!
//! The [`Glyph`] is the basic unit of data, each of which begins with an 8-byte
//! header containing a length, type information, and, in a few cases (e.g.,
//! for 32-bit numbers) user data.
//!
//! - Glyphs are always a multiple of 8 bytes in length, though they may have
//!   extra zero padding in some cases (e.g., strings).  This allows us to
//!   maintain byte alignment for up to 64-bit primitive types.
//! - Glyph may be stored on the heap ([`BoxGlyph`]), optionally with reference
//!   counting ([`ArcGlyph`]), or parsed from some other buffer
//!   ([`ParsedGlyph`]).  Most more specific types are generic over these.
//! - The [`Glyph`] interface itself provides nothing more than (1) type
//!   information and (2) an array of bytes.
//! - Once written, glyphs are immutable.  This significantly simplifies
//!   implementation.
//!
//! # Types of Glyphs
//!
//! - Basic existential types, such as [`NothingGlyph`].
//! - Numeric types, such as [`IntGlyph`], [`UIntGlyph`], and [`FloatGlyph`].
//! - Basic compound types, such as [`VecGlyph`], [`TupleGlyph`], and
//!   [`MapGlyph`].
//! - Structured types, such as [`ObjGlyph`] and [`DocGlyph`].
//! - Cryptography types, such as [`HashGlyph`], [`SignatureGlyph`] and
//    TODO: Add glyph types for passwords and keys
//! - Other useful types, such as [`UUIDGlyph`].

#![no_std]
// Used to allow const generics in trait APIs.
#![feature(generic_const_exprs)]
// Used to enable testing with no_std
#![feature(test)]
// Used to allow specialized vector encoding for slices of primitives.
#![feature(specialization)]
// Used for BoxGlyph and ArcGlyph
#![feature(allocator_api)]
// Used for generated documentation to reference feature requirements.
#![feature(doc_cfg)]
// Used by specialization feature
#![allow(incomplete_features)]
// Warnings disabled while in concept development.
#![allow(dead_code)]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
extern crate test;

/// Internal Macros
#[macro_use]
mod macros;

#[deny(missing_docs)]
pub mod basic;

#[deny(missing_docs)]
pub mod collections;

#[allow(missing_docs)]
pub mod crypto;

#[deny(missing_docs)]
mod dynamic;

#[allow(missing_docs)]
// #[cfg(feature = "glifs")]
pub mod glifs;
#[deny(missing_docs)]
mod glyph;
#[deny(missing_docs)]
pub mod misc;
#[deny(missing_docs)]
pub mod zerocopy;

#[warn(missing_docs)]
#[cfg(feature = "serde")]
mod serde;
#[cfg(feature = "serde")]
#[warn(missing_docs)]
#[doc(cfg(feature = "serde"))]
pub use serde::{
  de::glyph_serde_deserialize,
  ser::{glyph_new_serde, glyph_serde_length, glyph_serde_serialize},
};

#[deny(missing_docs)]
pub mod structured;

#[allow(missing_docs)]
mod util;

pub use self::glyph::*;
