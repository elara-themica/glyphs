//! Collections types, including tuples, vectors, maps, and trees.
//!
//!
//! # Vector Glyphs and Basic Vector Glyphs
//!
//! There are two different types of glyphs used for storing a series of data
//! objects.
//!
//! - [`BasicVecGlyph`]s work like your standard vector and array types in most
//!   computer systems.  While they can store an arbitrary number of items, all
//!   items must be of the same type and length.  While this is an extremely
//!   efficient way of storing data that meets these criteria, is is sometimes
//!   necessary to store objects with varying lengths (e.g., strings) or type.
//! - [`VecGlyph`]s store a series of glyphs each of which can have an arbitrary
//!   type and length.  To maintain constant time access, it stores an offsets
//!   table with the location of each stored glyph.
//! 
//! When working with data that has a fixed type and length, it is considerably
//! more efficient to use a `BasicVecGlyph`.  Not only does it avoid the 
//! overhead of storing unused length and type metadata, it often allows zero
//! copy access to the entire array at once.  (E.g., turn a `&'a Glyph` into
//! an `&'a [U64]`, which can just be treated as a native `u64` on most modern
//! hardware.)  In addition, we only need to perform type and bounds checking
//! once for the entire array.
//! 
//! In most cases, you should just be able to use the standard container types
//! like `&[T]` or `Vec<T>` and there should be [`ToGlyph`] and [`TryFrom`]
//! implementation that do the right thing.  However, should you want to 
//! (1) override the behavior or (2) use other types of containers, we provide 
//! adapter types that can be used for writing these glyphs correctly in your
//! preferred format.
//! 
//! [`VecGlyphWriter`] writes vector glyphs with items implementing `ToGlyph`, 
//! and [`BasicVecGlyphWriter`], writes basic vector glyphs with items 
//! implementing [`InBasicVec`]. Both types should work with any container type
//! where a reference to the container can be turned into an known-length 
//! iterator over `&T`.  Notably this includes both `&[T]`, `Vec<T>`, but you
//! can use any type that implements [`IntoIterator`] and related trait bounds.
//!
//! Unfortunately, blanket implementations for these types are currently a bit
//! problematic in rust, due to the lack of specialization in the language.  
//! Any blanket implementation of `ToGlyph` for type like `&[T]` where 
//! `T: ToGlyph` precludes having either (1) a specialized blanket `impl` for 
//! that same type where `T: ZeroCopy` or (2) a specialized `impl` for 
//! individual types.

mod map;
mod tuple;
mod vec;

pub use self::{map::*, tuple::*, vec::*};
