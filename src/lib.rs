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

pub mod basic;
pub mod collections;
pub mod crypto;
pub mod zerocopy;
// #[cfg(feature = "glifs")]
pub mod glifs;
mod glyph;
pub mod misc;

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

pub mod structured;
mod util;

pub use self::glyph::*;
