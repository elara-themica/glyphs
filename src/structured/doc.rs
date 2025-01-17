//! Documents and related types for semi-structured data.

use crate::{
  crypto::GlyphHash,
  glyph_close, glyph_read,
  zerocopy::{ZeroCopy, U16},
  FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader, GlyphPtr, GlyphType,
  ParsedGlyph, ToGlyph,
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
  pub fn new(num_old_versions: usize) -> Result<DocGlyphHeader, GlyphErr> {
    let num_old_versions: U16 = num_old_versions
      .try_into()
      .map_err(|_| GlyphErr::DocOldVersionsOverflow(num_old_versions))?;
    Ok(DocGlyphHeader {
      doc_glyph_version: 0,
      reserved_0: Default::default(),
      num_old_versions,
      reserved_1: Default::default(),
    })
  }
}

/// A Specific Version of a Document in a Collection.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct DocVer {
  document: GlyphHash,
  from_tx:  GlyphHash,
}

unsafe impl ZeroCopy for DocVer {}

impl DocVer {
  /// Creates a new `DocVer` instance.
  pub fn new(document: GlyphHash, from_tx: GlyphHash) -> Self {
    DocVer { document, from_tx }
  }

  /// Returns a reference to the document's `GlyphHash`.
  pub fn document(&self) -> &GlyphHash {
    &self.document
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
pub struct Document<I, B> {
  id:            I,
  prev_versions: SmallVec<DocVer, 2>,
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
  pub fn replace(id: I, body: B, replaces: &[DocVer]) -> Document<I, B> {
    let mut prev_versions =
      SmallVec::<DocVer, 2>::with_capacity(replaces.len());
    for ver in replaces {
      prev_versions.push(*ver);
    }
    Document {
      id,
      body,
      prev_versions,
    }
  }
}

impl<I, B> Document<I, B> {
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
  pub fn update<'a, 'b, G>(
    parent: &'a DocGlyph<G>,
    previous_versions: impl Iterator<Item = &'b DocVer>,
  ) -> Result<Document<I, B>, GlyphErr>
  where
    G: Glyph,
    I: FromGlyph<ParsedGlyph<'a>> + ToGlyph,
    B: FromGlyph<ParsedGlyph<'a>> + ToGlyph,
  {
    let id_glyph = parent.id_glyph();
    let body_glyph = parent.body_glyph();

    let id = I::from_glyph(id_glyph)?;
    let body = B::from_glyph(body_glyph)?;

    let prev_versions: SmallVec<DocVer, 2> =
      previous_versions.map(|v| *v).collect();
    Ok(Document {
      id,
      prev_versions,
      body,
    })
  }
}

impl<I, B> Document<I, B> {
  /// Returns a reference to the document's ID.
  pub fn id(&self) -> &I {
    &self.id
  }

  /// Returns a reference to the document's body.
  pub fn body(&self) -> &B {
    &self.body
  }

  /// Returns a mutable reference to the document's body.
  pub fn body_mut(&mut self) -> &mut B {
    &mut self.body
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

    let dgh = DocGlyphHeader::new(self.prev_versions().len())?;
    dgh.bbwr(target, cursor)?;

    DocVer::bbwrs(self.prev_versions(), target, cursor)?;

    // Write ID and body.
    self.id.glyph_encode(target, cursor)?;
    self.body.glyph_encode(target, cursor)?;

    // Write the glyph header.
    glyph_close(GlyphType::Document, target, offset, cursor, false)
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
  parents: NonNull<[DocVer]>,
  // SAFETY: These aren't actually 'static; they're internal self-references.
  id:      GlyphPtr,
  body:    GlyphPtr,
}

impl<G: Glyph> DocGlyph<G> {
  /// Returns a slice of hashes of previous versions of this document.
  pub fn previous_versions(&self) -> &[DocVer] {
    // SAFETY: Self-reference to self.glyph, which is immutable.
    unsafe { self.parents.as_ref() }
  }

  /// Returns the document's ID
  pub fn id_glyph(&self) -> ParsedGlyph {
    // SAFETY: Binds to lifetime of self.
    unsafe { self.id.deref() }
  }

  /// Returns the document's body
  pub fn body_glyph(&self) -> ParsedGlyph {
    // SAFETY: Binds to lifetime of self.
    unsafe { self.body.deref() }
  }
}

impl<'a> DocGlyph<ParsedGlyph<'a>> {
  /// Returns the document's ID, parsed from an underlying buffer.
  pub fn id_parse(&self) -> ParsedGlyph<'a> {
    // SAFETY: Bound to lifetime of underlying parsed glyph
    unsafe { self.body.deref() }
  }

  /// Returns the document's body, parsed from an underlying buffer.
  pub fn body_parse(&self) -> ParsedGlyph<'a> {
    // SAFETY: Bound to lifetime of underlying parsed glyph
    unsafe { self.body.deref() }
  }
}

impl<G: Glyph> FromGlyph<G> for DocGlyph<G> {
  fn from_glyph(source: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(err) = source.header().confirm_type(GlyphType::Document) {
      return Err(err.into_fge(source));
    }
    let content = source.content_padded();
    let cursor = &mut 0;

    let dgh = match DocGlyphHeader::bbrf(content, cursor) {
      Ok(header) => header,
      Err(err) => return Err(err.into_fge(source)),
    };
    let nov = u16::from(dgh.num_old_versions) as usize;
    let ov = match DocVer::bbrfs(content, cursor, nov) {
      Ok(versions) => versions,
      Err(err) => return Err(err.into_fge(source)),
    };
    // SAFETY: This internal self-reference must not escape without being bound
    // to the lifetime of 'self, and
    let id_glyph = match glyph_read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(err.into_fge(source)),
    };
    let id = GlyphPtr::from_parsed(id_glyph);
    let body_glyph = match glyph_read(content, cursor) {
      Ok(glyph) => glyph,
      Err(err) => return Err(err.into_fge(source)),
    };
    let body = GlyphPtr::from_parsed(body_glyph);

    let parents = NonNull::from(ov);

    Ok(DocGlyph {
      glyph: source,
      parents,
      id,
      body,
    })
  }
}

impl<G: Glyph> Debug for DocGlyph<G> {
  fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
    let mut b = f.debug_struct("DocGlyph");
    b.field("replaces", &self.previous_versions());
    b.field("id", &self.id_glyph());
    b.field("body", &self.body_glyph());
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
  use std::{dbg, iter, println};

  #[bench]
  fn glyph_doc_merkle_chain(b: &mut Bencher) -> Result<(), GlyphErr> {
    init_test_logger();

    let root = Document::new((), ());
    let rg = glyph_new(&root)?;
    dbg!(&rg);
    let rg = DocGlyph::from_glyph(rg)?;
    dbg!(&rg);
    let updated =
      Document::<(), ()>::update(&rg, iter::once(&Default::default()))?;
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

      let updated =
        Document::<(), ()>::update(&ug, iter::once(&Default::default()))?;
      updated.glyph_encode(target, cursor)?;

      while *cursor + ug_len < BENCH_BUF_SIZE {
        let prev_glyph = glyph_read(target, prev_offset)?;
        let prev_glyph = DocGlyph::from_glyph(prev_glyph)?;
        let updated = Document::<(), ()>::update(
          &prev_glyph,
          iter::once(&Default::default()),
        )?;
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

    // println!(
    //   "Version of the first glyph is {:?}",
    //   first_doc_glyph.version()
    // );
    println!(
      "It has {:?} parents",
      first_doc_glyph.previous_versions().len()
    );

    let mut second_doc = Document::<u32, String>::update(
      &first_doc_glyph,
      iter::once(&Default::default()),
    )?;
    second_doc.set_body(String::from("7 (good) times 6 (evil)"));

    let second_glyph = glyph_new(&second_doc)?;
    println!("Second glyph encoded as: \n {:?}", &second_glyph);

    let second_doc_glyph = DocGlyph::from_glyph(second_glyph)?;
    std::dbg!(&second_doc_glyph);
    // println!("Its version is: {:?}", second_doc_glyph.glyph());

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
