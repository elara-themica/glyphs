//! A semi-structured zero-copy data format.
//!
//! # Overview
//!
//! The _Glyphs_ data format is a semi-structured zero-copy data format,
//! designed for use in large distributed systems.  Its name is inspired by the
//! human language term of the same name, which represents a unit of written
//! meaning (e.g., letters, ideograms, etc...).  Similarly, this data format
//! uses the term "glyph" to denote a unit of meaning in computer systems.
//!
//! - __Semi-Structured__.  The Glyphs data format emphasizes what's known as
//!   [semi-structured data](https://en.wikipedia.org/wiki/Semi-structured_data).
//!   Semi-structured types do not rigidly define structure (like rows in a
//!   relational database table) where the types, elements, and meanings are
//!   defined (and, thus, inherently constrained) by some larger set of data
//!   to which it belongs.
//! - __Rich Type System__.  However, in comparison to common semi-structured
//!   types like JSON and XML, Glyphs has a larger number of types used to
//!   standardize and label different types of data. For example, while JSON
//!   typically would store a UUID or a date as a string, and depend on context
//!   and application logic to understand this semantic meaning.  In Glyphs,
//!   these are first-class types, each with their own type id (so they can be
//!   identified) and defined format.
//! - __Zero Copy__.  It is also a binary format, designed to be used by
//!   machines directly _without deserialization_ where possible.  For example,
//!   integers are stored in little-endian format, matching the in-memory format
//!   of modern CPUs.
//! - __High Performance__.  Because deserialization overhead in data-intensive
//!   applications can account for a significant portion of CPU use, a zero-copy
//!   format can be dramatically more efficient in many cases.  For example,
//!   a 2024 M4 Macbook can decode a series of small strings and confirm valid
//!   UTF-8 at ~15GB/s; an order of magnitude faster than many other systems.
//!   In addition, we can navigate large data structures only decoding
//!   specifically what we need.  For example, should we want to index a set of
//!   document glyphs where the identifier accounts for 5% of its length, we'll
//!   be ~200x faster than if we were decoding JSON objects--likely limited only
//!   by memory bandwidth.  (Based on claimed deserialization speed of
//!   `serde_json` as of July 2025.)
//!
//! # The Glyph
//!
//! The [`Glyph`] is the basic unit of data.  Each begins with an 8-byte
//! header describing its version, length, and the type of data contained.
//! For short glyphs, half of this header (i.e., 4 bytes) can be used for
//! content.
//!
//! - Once a glyph has been written, its contents are immutable.
//! - Glyphs are always a multiple of 8 bytes in length, though they may have
//!   extra zero padding in some cases (e.g., strings).  This allows us to
//!   maintain alignment for up to 64-bit primitive types.
//! - The [`Glyph`] type is basically just a `[u8]` with some extra invariants.
//!   - The buffer is always at least 8 bytes long.
//!   - The buffer's length is always a multiple of 8 bytes.
//!   - The buffer is always aligned in-memory to 8 bytes.
//!   - The first 8 bytes contain a [`GlyphHeader`].
//!   - The length of the buffer matches the length of the glyph as described
//!     in that header.
//! - Glyphs can be decoded into more specific types (e.g., [`VecGlyph`]) which
//!   then provide the additional functionality provided by that type.  In some
//!   cases glyphs can be decoded into native types (e.g., `str`, `[u64]`).
//! - When the type of glyph is not known in advance, [`DynGlyph`] provides
//!   an enumeration over the available types.
//! - [`Glyph`] is an unsized type.  When writing a new glyph, it will typically
//!   be into a heap-allocated container like [`Box`] or [`Arc`].  When reading,
//!   from some other buffer, they can be accessed as a `&Glyph` and sometimes
//!   as references to native types like `&str`.
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
//!

#![cfg_attr(not(feature = "std"), no_std)]

// Used by specialization feature
#![allow(incomplete_features)]
// Warnings disabled while in concept development.
#![allow(dead_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Internal Macros
#[macro_use]
mod macros;

#[warn(missing_docs)]
pub mod basic;

#[warn(missing_docs)]
pub mod collections;

#[allow(missing_docs)]
pub mod crypto;

#[warn(missing_docs)]
mod dynamic;

#[allow(missing_docs)]
// #[cfg(feature = "glifs")]
pub mod glifs;
#[warn(missing_docs)]
mod glyph;
#[warn(missing_docs)]
pub mod misc;
#[warn(missing_docs)]
pub mod zerocopy;

#[warn(missing_docs)]
pub mod structured;

#[allow(missing_docs)]
mod util;

pub use self::glyph::*;
