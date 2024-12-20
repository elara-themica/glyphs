//! Documents and related types for semi-structured data.

use crate::{
  crypto::GlyphHash,
  glyph_close, glyph_read,
  util::MemoizedInvariant,
  zerocopy::{ZeroCopy, U16, U64},
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ParsedGlyph, ToGlyph,
};
use core::{
  borrow::Borrow,
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
};
use smallvec::SmallVec;

/// The specific type header for document glyphs.
///
/// - `doc_glyph_version` must be equal to zero (experimental version)
/// - `num_old_versions` indicates the number of previous versions this item
///   is replacing (usually one)
#[repr(packed)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct DocGlyphHeader {
  doc_glyph_version: u8,
  reserved_0:        u8,
  num_old_versions:  U16,
  reserved_1:        [u8; 4],
}

unsafe impl ZeroCopy for DocGlyphHeader {}

impl DocGlyphHeader {
  /// Creates a new [`DocGlyphHeader`].
  pub fn new(num_old_versions: u16) -> DocGlyphHeader {
    DocGlyphHeader {
      doc_glyph_version: 0,
      reserved_0:        Default::default(),
      num_old_versions:  U16::from(num_old_versions),
      reserved_1:        Default::default(),
    }
  }
}

/// Describes version of a document, consisting of a `u64` serial number and
/// a cryptographic hash.
///
/// - A document's serial number equal to one greater than the highest serial
///   number of its (potentially multiple) parents/previous versions.  A
///   document with no previous versions has a serial number of zero.
/// - The hash is the document's cryptographic hash.
///
/// Note that implied in this definition, a document's own version (1) can be
/// reliably calculated from its content but (2) cannot be stored or asserted
/// directly in the document itself, due to the hash requirement.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
#[repr(packed)]
pub struct DocVer {
  pub serial: U64,
  pub hash:   GlyphHash,
}

unsafe impl ZeroCopy for DocVer {}

impl Debug for DocVer {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    write!(f, "DocVer({:?}/{})", &self.hash, &self.serial)
  }
}

/// A simple document type suitable for encoding into (and decoding from) a
/// [`DocGlyph`].
///
/// - Documents consist of an ID and a Body, both of which must be encodable to
///   glyphs.
/// - A previous version is only required when updating a document (with the
///   same ID) to a different body.
/// - Multiple previous versions are only required when a new version replaces
///   two or more previous versions (e.g., merging simultaneous / partitioned
///   changes).
#[cfg(feature = "alloc")]
#[derive(Debug)]
pub struct Document<I, B>
where
  I: ToGlyph,
  B: ToGlyph,
{
  id:            I,
  prev_versions: SmallVec<DocVer, 4>,
  body:          B,
}

#[cfg(feature = "alloc")]
impl<I, B> Document<I, B>
where
  I: ToGlyph,
  B: ToGlyph,
{
  /// Create a new document (i.e., no modification history)
  pub fn new(id: I, body: B) -> Document<I, B> {
    Document {
      id,
      prev_versions: Default::default(),
      body,
    }
  }

  /// Create a new document to replace older versions.
  pub fn replace(id: I, body: B, replaces: &[GlyphHash]) -> Document<I, B> {
    let mut prev_versions =
      SmallVec::<DocVer, 4>::with_capacity(replaces.len());
    for ver in replaces {
      prev_versions.push(*ver);
    }
    Document {
      id,
      prev_versions,
      body,
    }
  }
}

impl<I, B> Document<I, B>
where
  I: ToGlyph + 'static,
  B: ToGlyph + 'static,
{
  /// This function reads a(n immutable) [`DocGlyph`] into a new (mutable)
  /// `Document`, listing the original document as an old version.
  ///
  /// This function will typically need to be called with the destination type
  /// explicitly specified, and the concrete types for `I`, `T`, and `B` will
  /// need to match what's actually in the glyph.  If the specified types do
  /// not match the actual contents of the glyph, or if those glyphs cannot be
  /// decoded, this function will return a `GlyphErr`.
  ///
  /// The example below creates a Merkle chain for a document with a nothing
  /// glyph for the id, type, and body.  While these types
  ///
  // FIXME: fix document example
  //   ```
  //   use glyphs::*;
  //   use glyphs::collections::*;
  //
  //   let root = Document::new(2u32, 4u32);
  //   let mut prev_glyph = glyph_new(&root).unwrap();
  //   println!("Root: {:?}", &prev_glyph);
  //
  //   for i in 0u32..3 {
  //     // Recognize the previous glyph as a [`DocGlyph`]
  //     let dg = DocGlyph::from_glyph(prev_glyph.borrow()).unwrap();
  //     // Decode into a [`Document`] object.
  //     let mut doc: Document<u32, u32> = Document::update(&dg).unwrap();
  //     // Update the contents (to i*id^2)
  //     doc.set_body(i * doc.id() * doc.id());
  //     // Encode this new version and set it as the source for next iteration.
  //     prev_glyph = glyph_new(&doc).unwrap();
  //     println!("Next: {:?}", &prev_glyph);
  //   }
  //   ```
  pub fn update<'a, G>(
    parent: &'a DocGlyph<G>,
  ) -> Result<Document<I, B>, GlyphErr>
  where
    G: Glyph,
    I: FromGlyph<ParsedGlyph<'a>> + ToGlyph + 'static,
    B: FromGlyph<ParsedGlyph<'a>> + ToGlyph + 'static,
    // TODO: Is the 'static really required here?
  {
    let id_glyph = parent.id();
    let body_glyph = parent.body();

    let id = I::from_glyph(id_glyph)?;
    let body = B::from_glyph(body_glyph)?;

    let mut prev_versions = SmallVec::new();
    prev_versions.push(*parent.version());
    Ok(Document {
      id,
      prev_versions,
      body,
    })
  }
}

impl<I, B> Document<I, B>
where
  I: ToGlyph,
  B: ToGlyph,
{
  /// Returns a reference to the document's ID.
  pub fn id(&self) -> &I {
    &self.id
  }

  /// Returns a reference to the document's body.
  pub fn body(&self) -> &B {
    &self.body
  }

  /// Returns a reference to the vector of previous versions, if any.
  pub fn prev_versions(&self) -> &[DocVer] {
    self.prev_versions.borrow()
  }

  /// Changes the document's ID, resetting previous versions, if any.
  ///
  /// - This requires the new ID be of the same type.  If a different type is
  ///   needed for the new ID, create a new document instead.
  /// - If there are any previous versions, they will be cleared.
  pub fn rename(&mut self, id: I) {
    self.prev_versions.clear();
    self.id = id;
  }

  /// Replaces the document body.
  pub fn set_body(&mut self, body: B) {
    self.body = body;
  }
}

impl<I, B> ToGlyph for Document<I, B>
where
  I: ToGlyph,
  B: ToGlyph,
{
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();

    let dgh = DocGlyphHeader::new(self.prev_versions().len().try_into()?);
    dgh.bbwr(target, cursor)?;

    DocVer::bbwrs(self.prev_versions(), target, cursor)?;

    // Write ID and body.
    self.id.glyph_encode(target, cursor)?;
    self.body.glyph_encode(target, cursor)?;

    // Write the glyph header.
    glyph_close(GlyphType::DocumentGlyph, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<DocGlyphHeader>()
      + size_of::<DocVer>() * self.prev_versions.len()
      + self.id.glyph_len()
      + self.body.glyph_len()
  }
}

/// A semi-structured database document glyph.
///
/// A document consists of an ID, a Body, and a list of previous versions (if
/// any) with the same ID that this document replaces.
///
// SAFETY:
//
// The following invariants must hold:
//
// - The [`DocGlyphHeader`] at the head of the glyph's contents is valid.
// - The ID, Type, and Body are valid as _glyphs_.  This means they are fully
//   contained within the `DocGlyph`'s buffer and have valid headers.  It does
//   not mean the _contents_ are valid.  (e.g., the body may be a valid glyph
//   but an invalid `VecGlyph`)
// - The list of previous `DocVer`s is valid and fully contained within the
//   `DocGlyph`'s buffer.
pub struct DocGlyph<G: Glyph> {
  glyph:   G,
  serial:  u64,
  own_ver: MemoizedInvariant<DocVer>,
  parents: NonNull<[DocVer]>,
  // SAFETY: These aren't actually 'static; they're internal self-references.
  id:      ParsedGlyph<'static>,
  body:    ParsedGlyph<'static>,
}

impl<G: Glyph> DocGlyph<G> {
  /// Returns a slice of hashes of previous versions of this document.
  pub fn previous_versions(&self) -> &[GlyphHash] {
    // SAFETY: Self-reference to self.glyph, which is immutable.
    unsafe { self.parents.as_ref() }
  }

  /// Returns the document's ID
  pub fn id_glyph(&self) -> ParsedGlyph {
    // SAFETY: Binds to lifetime of self.
    self.id.clone()
  }

  /// Returns the document's body
  pub fn body_glyph(&self) -> ParsedGlyph {
    // SAFETY: Binds to lifetime of self.
    self.body.clone()
  }

  /// Returns the version of this document.
  pub fn version(&self) -> &DocVer {
    self.own_ver.get(|| {
      let hash = self.glyph.glyph_hash();
      DocVer {
        serial: U64::from(self.serial),
        hash,
      }
    })
  }

  pub fn serial(&self) -> u64 {
    self.serial
  }
}

impl<'a> DocGlyph<ParsedGlyph<'a>> {
  /// Returns the document's ID, parsed from an underlying buffer.
  pub fn id_parse(&self) -> ParsedGlyph<'a> {
    // SAFETY: Bound to lifetime 'a
    self.id.clone()
  }

  /// Returns the document's body, parsed from an underlying buffer.
  pub fn body_parse(&self) -> ParsedGlyph<'a> {
    // SAFETY: Bound to lifetime 'a
    self.body.clone()
  }
}

impl<G: Glyph> FromGlyph<G> for DocGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, GlyphErr> {
    source.header().confirm_type(GlyphType::DocumentGlyph)?;
    let content = source.content_padded();
    let cursor = &mut 0;

    let dgh = DocGlyphHeader::bbrf(content, cursor)?;
    let nov = u16::from(dgh.num_old_versions) as usize;
    let ov = DocVer::bbrfs(content, cursor, nov)?;
    let mut serial = 0;
    for v in ov {
      if serial <= v.serial.get() {
        serial = u64::from(v.serial) + 1;
      }
    }
    // SAFETY: This internal self-reference must not escape without being bound
    // to the lifetime of 'self, and
    let id = unsafe { glyph_read(content, cursor)?.detach() };
    let body = unsafe { glyph_read(content, cursor)?.detach() };

    let parents = NonNull::from(ov);

    Ok(DocGlyph {
      glyph: source,
      serial,
      own_ver: MemoizedInvariant::empty(),
      parents,
      id,
      body,
    })
  }
}

// #[glyphs_derive::from_ord(Eq, PartialEq, PartialOrd)]
// impl<G> Ord for DocGlyph<G>
// where
//   G: PinnedGlyph,
// {
//   fn cmp(&self, other: &Self) -> Ordering {
//     glyph_sort(&self.id(), &other.id())
//       .then(self.serial.cmp(&other.serial))
//       .then(self.glyph.glyph_hash().cmp(&other.glyph.glyph_hash()))
//   }
// }

impl<G: Glyph> Debug for DocGlyph<G> {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut b = f.debug_struct("DocGlyph");
    b.field("id", &self.id());
    b.field("own_ver", &self.version());
    b.field("parents", &self.parents());
    b.field("body", &self.body());
    b.finish()
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    glyph_new,
    util::{init_test_logger, BENCH_BUF_SIZE},
  };
  use ::test::Bencher;
  use alloc::string::String;
  use std::{dbg, println};

  #[bench]
  fn glyph_doc_merkle_chain(b: &mut Bencher) -> Result<(), GlyphErr> {
    init_test_logger();

    let root = Document::new((), ());
    let rg = glyph_new(&root)?;
    dbg!(&rg);
    let rg = DocGlyph::from_glyph(rg)?;
    dbg!(&rg);
    let updated = Document::<(), ()>::update(&rg)?;
    let ug = glyph_new(&updated)?;
    dbg!(&ug);
    let ug_len = ug.glyph_len();
    let ug = DocGlyph::from_glyph(Glyph::borrow(&ug))?;
    dbg!(&ug);

    b.bytes = BENCH_BUF_SIZE as u64;
    b.iter(|| {
      let mut buffer = [0u8; BENCH_BUF_SIZE];
      let target = &mut buffer[..];
      let cursor = &mut 0usize;
      let prev_offset = &mut 0usize;

      let updated = Document::<(), ()>::update(&ug)?;
      updated.glyph_encode(target, cursor)?;

      while *cursor + ug_len < BENCH_BUF_SIZE {
        let prev_glyph = glyph_read(target, prev_offset)?;
        let prev_glyph = DocGlyph::from_glyph(prev_glyph)?;
        let updated = Document::<(), ()>::update(&prev_glyph)?;
        updated.glyph_encode(target, cursor)?;
      }

      Ok::<(), GlyphErr>(())
    });

    Ok(())
  }

  #[test]
  fn glyph_doc() -> Result<(), GlyphErr> {
    let first_doc = Document::new(42u32, "Life, the Universe, and Everything");
    let first_glyph = glyph_new(&first_doc)?;
    println!("First glyph encoded as:\n {:?}", &first_glyph);

    let first_doc_glyph = DocGlyph::from_glyph(first_glyph)?;

    println!(
      "Version of the first glyph is {:?}",
      first_doc_glyph.version()
    );
    println!("It has {:?} parents", first_doc_glyph.parents().len());

    let mut second_doc = Document::<u32, String>::update(&first_doc_glyph)?;
    second_doc.set_body(String::from("7 (good) times 6 (evil)"));

    let second_glyph = glyph_new(&second_doc)?;
    println!("Second glyph encoded as: \n {:?}", &second_glyph);

    let second_doc_glyph = DocGlyph::from_glyph(second_glyph)?;
    println!("Its version is: {:?}", second_doc_glyph.version());

    Ok(())
  }

  // #[test]
  // fn doc_glyph_sorting() -> Result<(), GlyphErr> {
  //   let d1 = Document::new(1i32, "a");
  //   let d2 = Document::new(1i32, "b");
  //   let d3 = Document::new(2i32, "a");
  //   let d4 = Document::new(1i32, "a");
  //
  //   let d1g = glyph_new(&d1)?;
  //   let d2g = glyph_new(&d2)?;
  //   let d3g = glyph_new(&d3)?;
  //   let d4g = glyph_new(&d4)?;
  //
  //   assert_eq!(glyph_sort(&d1g.borrow(), &d2g.borrow()), Ordering::Less);
  //   assert_eq!(glyph_sort(&d2g.borrow(), &d3g.borrow()), Ordering::Less);
  //   assert_eq!(glyph_sort(&d3g.borrow(), &d4g.borrow()), Ordering::Greater);
  //   assert_eq!(glyph_sort(&d1g.borrow(), &d4g.borrow()), Ordering::Equal);
  //
  //   let d1dg = DocGlyph::from_glyph(d1g.borrow())?;
  //   let d5 =
  //     Document::new_versioned(1i32, slice::from_ref(d1dg.version()), "a");
  //   dbg!(&d5);
  //   let d5g = glyph_new(&d5)?;
  //
  //   dbg!(&d1g);
  //   dbg!(&d5g);
  //
  //   assert_eq!(glyph_sort(&d1g.borrow(), &d5g.borrow()), Ordering::Less);
  //   Ok(())
  // }
}
