use crate::{
  crypto::GlyphHash,
  glyph_close,
  util::{debug::ShortHexDump, LogErr, SortedSliceRef},
  zerocopy::{ZeroCopy, U16},
  FromGlyph, Glyph, GlyphErr, GlyphHeader, GlyphType, ToGlyph,
};
use core::{
  fmt::{Debug, Formatter},
  mem::size_of,
  ptr::NonNull,
};
use ed25519_dalek::{
  Signature, Signer, SigningKey, Verifier, VerifyingKey, PUBLIC_KEY_LENGTH,
  SIGNATURE_LENGTH,
};
use log::Level;

#[derive(Copy, Clone, Eq, Debug, Ord, PartialEq, PartialOrd)]
#[repr(packed)]
pub struct GlifsDelete {
  object_hash: GlyphHash,
  source_tx:   GlyphHash,
}

/// SAFETY: All components are zero copy
unsafe impl ZeroCopy for GlifsDelete {}

impl GlifsDelete {
  pub fn new(object_hash: GlyphHash, source_tx: GlyphHash) -> Self {
    Self {
      object_hash,
      source_tx,
    }
  }

  pub fn object_hash(&self) -> &GlyphHash {
    &self.object_hash
  }

  pub fn source_tx(&self) -> &GlyphHash {
    &self.source_tx
  }
}

/// Header for [`TxLogGlyph`].
///
/// - 16 bytes in length
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(packed)]
struct TxLogHeader {
  /// Must be 0 for the experimental version
  format_version: u8,

  reserved: [u8; 5],

  /// The number of immediately preceding transactions.
  ///
  /// For the total # of transactions, see `tx_height`.
  num_previous_transactions: U16,

  /// The number of glyphs added that wil not require specific cryptographic
  /// verification to delete.
  num_glyphs_added: U16,

  /// The number of glyphs deleted not requiring cryptographic verification.
  num_glyphs_deleted: U16,

  /// The number of extents added that will not require specific cryptographic
  /// verification to delete.
  num_extents_added: U16,

  /// The number of extents deleted not requiring cryptographic verification.
  num_extents_deleted: U16,
}

// SAFETY: All components are zero copy
unsafe impl ZeroCopy for TxLogHeader {}

impl TxLogHeader {
  pub fn num_previous_transactions(&self) -> usize {
    self.num_previous_transactions.get() as usize
  }

  pub fn num_glyphs_added(&self) -> usize {
    self.num_glyphs_added.get() as usize
  }

  pub fn num_glyphs_deleted(&self) -> usize {
    self.num_glyphs_deleted.get() as usize
  }

  pub fn num_extents_added(&self) -> usize {
    self.num_extents_added.get() as usize
  }

  pub fn num_extents_deleted(&self) -> usize {
    self.num_extents_deleted.get() as usize
  }
}

pub struct TxLogGlyph<B>
where
  B: Glyph,
{
  glyph:           B,
  previous_txs:    NonNull<[GlyphHash]>,
  collection:      NonNull<GlyphHash>,
  pk_bytes:        NonNull<[u8; PUBLIC_KEY_LENGTH]>,
  glyphs_added:    NonNull<[GlyphHash]>,
  glyphs_deleted:  NonNull<[GlifsDelete]>,
  extents_added:   NonNull<[GlyphHash]>,
  extents_deleted: NonNull<[GlifsDelete]>,
  sig_bytes:       NonNull<[u8; SIGNATURE_LENGTH]>,
  sig_valid:       bool,
}

impl<B> TxLogGlyph<B>
where
  B: Glyph,
{
  pub fn previous_txs(&self) -> &[GlyphHash] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.previous_txs.as_ref() }
  }

  pub fn collection(&self) -> &GlyphHash {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.collection.as_ref() }
  }

  pub fn pk_bytes(&self) -> &[u8; 32] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.pk_bytes.as_ref() }
  }

  pub fn glyphs_added(&self) -> &[GlyphHash] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.glyphs_added.as_ref() }
  }

  pub fn glyphs_deleted(&self) -> &[GlifsDelete] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.glyphs_deleted.as_ref() }
  }

  pub fn extents_added(&self) -> &[GlyphHash] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.extents_added.as_ref() }
  }

  pub fn extents_deleted(&self) -> &[GlifsDelete] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.extents_deleted.as_ref() }
  }

  pub fn sig_bytes(&self) -> &[u8; 64] {
    // SAFETY: Internal zero-copy self-reference, bound to &_ lifetime.
    unsafe { self.sig_bytes.as_ref() }
  }

  pub fn sig_valid(&self) -> bool {
    self.sig_valid
  }
}

impl<B> FromGlyph<B> for TxLogGlyph<B>
where
  B: Glyph,
{
  fn from_glyph(glyph: B) -> Result<Self, GlyphErr> {
    glyph.confirm_type(GlyphType::GlifsTxLog)?;
    let source = glyph.content_padded();
    let cursor = &mut 0;

    let header = TxLogHeader::bbrf(source, cursor)?;
    let collection = GlyphHash::bbrf(source, cursor)?;
    let pk_bytes: &[u8; 32] = u8::bbrfa(source, cursor)?;
    let previous_tx =
      GlyphHash::bbrfs(source, cursor, header.num_previous_transactions())?;

    let glyphs_added =
      GlyphHash::bbrfs(source, cursor, header.num_glyphs_added())?;
    let glyphs_deleted =
      GlifsDelete::bbrfs(source, cursor, header.num_glyphs_deleted())?;
    let extents_added =
      GlyphHash::bbrfs(source, cursor, header.num_extents_added())?;
    let extents_deleted =
      GlifsDelete::bbrfs(source, cursor, header.num_extents_deleted())?;
    let signed_content = &source[..*cursor];

    let sig_bytes: &[u8; 64] = u8::bbrfa(source, cursor)?;

    let pk = VerifyingKey::from_bytes(&pk_bytes)
      .map_err(|_err| GlyphErr::Ed25519VerificationKeyInvalid)
      .log_err(Level::Error)?;
    let sig = Signature::from_bytes(&sig_bytes);
    let sig_valid = pk.verify(signed_content, &sig).is_ok();

    let previous_tx = NonNull::from(previous_tx);
    let collection = NonNull::from(collection);
    let pk_bytes = NonNull::from(pk_bytes);
    let glyphs_added = NonNull::from(glyphs_added);
    let glyphs_deleted = NonNull::from(glyphs_deleted);
    let extents_added = NonNull::from(extents_added);
    let extents_deleted = NonNull::from(extents_deleted);
    let sig_bytes = NonNull::from(sig_bytes);

    Ok(Self {
      glyph,
      previous_txs: previous_tx,
      collection,
      pk_bytes,
      glyphs_added,
      glyphs_deleted,
      extents_added,
      extents_deleted,
      sig_bytes,
      sig_valid,
    })
  }
}

impl<B> Debug for TxLogGlyph<B>
where
  B: Glyph,
{
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("TxLogGlyph");
    df.field("collection", self.collection());
    df.field("pk", &ShortHexDump(&self.pk_bytes()[..], 32));
    df.field("sig_valid", &self.sig_valid());
    df.field("previous_txs", &self.previous_txs());
    df.field("glyphs_added", &self.glyphs_added());
    df.field("glyphs_deleted", &self.glyphs_deleted());
    df.field("extents_added", &self.glyphs_added());
    df.field("extents_deleted", &self.extents_deleted());
    df.finish()
  }
}

pub struct TxLogEncoder<'a> {
  collection:            GlyphHash,
  previous_transactions: SortedSliceRef<'a, GlyphHash>,
  signing_key:           &'a SigningKey,

  glyphs_added:   SortedSliceRef<'a, GlyphHash>,
  glyphs_deleted: SortedSliceRef<'a, GlifsDelete>,

  extents_added:   SortedSliceRef<'a, GlyphHash>,
  extents_deleted: SortedSliceRef<'a, GlifsDelete>,
}

impl<'a> TxLogEncoder<'a> {
  pub fn new<P>(
    collection: GlyphHash,
    previous_txs: P,
    signing_key: &'a SigningKey,
  ) -> Self
  where
    P: Into<SortedSliceRef<'a, GlyphHash>>,
  {
    Self {
      collection,
      previous_transactions: previous_txs.into(),
      signing_key,
      glyphs_added: ().into(),
      glyphs_deleted: ().into(),
      extents_added: ().into(),
      extents_deleted: ().into(),
    }
  }

  pub fn set_glyphs_added<G>(&mut self, glyphs: G)
  where
    G: Into<SortedSliceRef<'a, GlyphHash>>,
  {
    self.glyphs_added = glyphs.into();
  }

  pub fn set_glyphs_deleted<D>(&mut self, deletes: D)
  where
    D: Into<SortedSliceRef<'a, GlifsDelete>>,
  {
    self.glyphs_deleted = deletes.into();
  }

  pub fn set_extents_added<E>(&mut self, extents: E)
  where
    E: Into<SortedSliceRef<'a, GlyphHash>>,
  {
    self.extents_added = extents.into();
  }

  pub fn set_extents_deleted<D>(&mut self, deletes: D)
  where
    D: Into<SortedSliceRef<'a, GlifsDelete>>,
  {
    self.extents_deleted = deletes.into();
  }
}

impl<'a> ToGlyph for TxLogEncoder<'a> {
  fn glyph_encode(
    &self,
    target: &mut [u8],
    cursor: &mut usize,
  ) -> Result<(), GlyphErr> {
    let offset = *cursor;
    *cursor += size_of::<GlyphHeader>();
    let content_offset = *cursor;
    TxLogHeader {
      format_version:            0,
      reserved:                  Default::default(),
      num_previous_transactions: self
        .previous_transactions
        .as_ref()
        .len()
        .try_into()?,
      num_glyphs_added:          self.glyphs_added.as_ref().len().try_into()?,
      num_glyphs_deleted:        self
        .glyphs_deleted
        .as_ref()
        .len()
        .try_into()?,
      num_extents_added:         self
        .extents_added
        .as_ref()
        .len()
        .try_into()?,
      num_extents_deleted:       self
        .extents_deleted
        .as_ref()
        .len()
        .try_into()?,
    }
    .bbwr(target, cursor)?;

    self.collection.bbwr(target, cursor)?;
    u8::bbwrs(self.signing_key.verifying_key().as_bytes(), target, cursor)?;
    GlyphHash::bbwrs(self.previous_transactions.as_ref(), target, cursor)?;

    GlyphHash::bbwrs(self.glyphs_added.as_ref(), target, cursor)?;
    GlifsDelete::bbwrs(self.glyphs_deleted.as_ref(), target, cursor)?;
    GlyphHash::bbwrs(self.extents_added.as_ref(), target, cursor)?;
    GlifsDelete::bbwrs(self.extents_deleted.as_ref(), target, cursor)?;
    let signed_content = &target[content_offset..*cursor];
    let sig = self.signing_key.sign(signed_content);
    u8::bbwrs(&sig.to_bytes()[..], target, cursor)?;

    glyph_close(GlyphType::GlifsTxLog, target, offset, cursor, false)
  }

  fn glyph_len(&self) -> usize {
    size_of::<GlyphHeader>()
      + size_of::<TxLogHeader>()
      + size_of::<GlyphHash>()
        * (self.previous_transactions.as_ref().len()
          + self.glyphs_added.as_ref().len()
          + self.extents_added.as_ref().len()
          + 2)
      + size_of::<GlifsDelete>()
        * (self.glyphs_deleted.as_ref().len()
          + self.extents_deleted.as_ref().len())
      + SIGNATURE_LENGTH
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::{
    crypto::{ed25519_keypair_generate, CryptographicHash},
    glyph_new,
    util::init_test_logger,
  };
  use rand::SeedableRng;
  use rand_chacha::ChaCha20Rng;
  use std::dbg;

  #[test]
  fn codec_tx_log() -> Result<(), GlyphErr> {
    init_test_logger();

    let mut rng = ChaCha20Rng::from_seed([32; 32]);
    let (sk, _pk) = ed25519_keypair_generate(&mut rng);
    let mut hashes = alloc::vec::Vec::new();
    for i in 0..10u8 {
      hashes.push(GlyphHash::from_hash_bytes([i; 32]))
    }
    let glyph_del = GlifsDelete::new(hashes[3], hashes[4]);
    let extent_del = GlifsDelete::new(hashes[5], hashes[6]);
    let mut tx = TxLogEncoder::new(hashes[9], &hashes[0], &sk);
    tx.set_glyphs_added(&hashes[1]);
    tx.set_extents_added(&hashes[2]);
    tx.set_glyphs_deleted(&glyph_del);
    tx.set_extents_deleted(&extent_del);

    let g = glyph_new(&tx)?;
    dbg!(&g);

    let txg = TxLogGlyph::from_glyph(g)?;
    dbg!(&txg);

    Ok(())
  }
}
