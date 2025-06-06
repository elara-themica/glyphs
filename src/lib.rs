//! Semi-structured zero-copy types used in the GLIFS data management system.
//!
//! # Overview
//!
//! The _glyphs_ data format is a semi-structured zero copy data format,
//! designed for use in large distributed systems.  Its name is inspired by the
//! human language term of the same name, which represents a unit of written
//! meaning (e.g., a letter).  Similarly, the data format uses the term
//! [`Glyph`] to represent a unit of meaning for a computer data system.
//!
//! - __Semi-Structured__.  The _glyphs_ data format is what's known as
//!   [semi-structured](https://en.wikipedia.org/wiki/Semi-structured_data).
//!   It does not have a rigidly defined structure (like a row in a relational
//!   database table) where types, elements, and meanings are defined by (and
//!   thus inherently constrained by) some larger set of data to which it
//!   belongs.  Instead, each object contains metadata that allows a flexible
//!   structure, like a JSON object (the equivalent of which would be an
//!   [`ObjGlyph`]).
//! - __Rich Type System__.  Glyphs have a larger number of types used to
//!   standardize and label different types of data.  For example, while JSON
//!   typically would store a UUID or a date as a string, and depend on context
//!   and application logic to understand this semantic meaning, these are
//!   first-class types in the glyphs format, with their own type identifiers
//!   and defined format.
//! - __Zero Copy__.  It is also a binary format, designed to be used by
//!   machines directly _without deserialization_.  Because deserialization
//!   overhead in data-intensive applications accounts for a significant
//!   portion of CPU use, a zero copy format can be dramatically more efficient
//!   in many cases.
//!
//! # The Glyph
//!
//! The [`Glyph`] is the basic unit of data, each of which begins with an 8-byte
//! header containing a length, type information, and, in a few cases (e.g.,
//! for 32-bit numbers) the meaningful data.
//!
//! - Glyphs are always a multiple of 8 bytes in length, though they may have
//!   extra zero padding in some cases (e.g., strings).  This allows us to
//!   maintain alignment for up to 64-bit primitive types.
//! - Glyph may be stored on the heap ([`BoxGlyph`]), optionally with reference
//!   counting ([`ArcGlyph`]), or parsed from some other buffer
//!   ([`ParsedGlyph`]).  Most more specific types are generic over these.
//! - The [`Glyph`] trait itself provides nothing more than (1) type
//!   information and (2) an array of bytes.  It is the more specific types that
//!   allow more semantically meaningful zero-copy access to contained
//!   information.  These are typically decoded using [`FromGlyph`], either
//!   directly from an expected type or dynamically using [`DynGlyph`].
//! - Glyphs can be re-written but are themselves immutable, just as any other
//!   serialized data.
//!
//! # Types of Glyphs
//!
//! - Basic types, e.g. [`IntGlyph`], [`UnitGlyph`] and [`StringGlyph`].
//! - Simple semantic types, e.g. [`DateTimeGlyph`] and [`UUIDGlyph`].
//! - Container types, e.g. [`VecGlyph`], [`MapGlyph`], and [`ObjGlyph`].
//! - Data system types, e.g. [`DocGlyph`],  that facilitate replication and
//!   synchronization.
//! - Native cryptographic types, e.g. [`HashGlyph`], [`SignatureGlyph`], and
//!   [`PasswordGlyph`].
//!
//! It is expected that the list of these types will grow somewhat over time.
//!

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
#![feature(pointer_is_aligned_to)]
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
