mod context;
mod glyph;
mod types;
mod update;

mod writers;

pub use self::{context::UpdateContext, glyph::*, types::*};

#[cfg(test)]
pub(super) mod tests {
  use super::*;
  use crate::{
    collections::climb::{
      glyph::CLiMBTreeNodeGlyph,
      writers::{CLiMBTreeNodeLenCalc, CLiMBTreeNodeWriter},
    },
    crypto::{CryptographicHash, GlyphHash},
    glyph_new_arc,
    util::{debug::HexDump, BloomFilter},
    zerocopy::I64,
    ArcGlyph, BoxGlyph, FromGlyph, GlyphErr, ToGlyph,
  };
  use rand::{Rng, RngCore, SeedableRng};
  use rand_chacha::ChaCha20Rng;
  use std::{
    collections::{BTreeMap, BTreeSet},
    dbg,
    vec::Vec,
  };

  pub fn random_sst(
    rng: &mut ChaCha20Rng,
  ) -> (GlyphHash, usize, BloomFilter<[u8; 128]>) {
    let target_hash = GlyphHash::random(rng);
    let target_len = rng.next_u32() as usize * 8;
    let mut target_bf = [0u8; 128];
    rng.fill_bytes(&mut target_bf);
    let bf_k = rng.next_u32() as u16 as usize;
    let bf = BloomFilter::new(target_bf, bf_k);
    (target_hash, target_len, bf)
  }

  pub fn random_pivot(
    rng: &mut ChaCha20Rng,
  ) -> (
    I64,
    GlyphHash,
    Vec<(GlyphHash, usize, BloomFilter<[u8; 128]>)>,
  ) {
    let mut child_sst_links = Vec::new();
    for _j in 16..19 {
      child_sst_links.push(random_sst(rng));
    }
    let pivot: i64 = rng.gen();
    let pivot = I64::from(pivot);
    let child_hash = GlyphHash::random(rng);
    (pivot, child_hash, child_sst_links)
  }

  pub fn random_tombstones(
    rng: &mut ChaCha20Rng,
    num_tombstones: usize,
  ) -> Vec<I64> {
    let mut tombstones = Vec::with_capacity(num_tombstones);
    for _ in 0..num_tombstones {
      let tombstone: i64 = rng.gen();
      let tombstone = I64::from(tombstone);
      tombstones.push(tombstone);
    }
    tombstones.sort_unstable();
    tombstones
  }

  pub fn random_entries(
    rng: &mut ChaCha20Rng,
    num_entries: usize,
  ) -> Vec<(I64, I64)> {
    let mut entries = Vec::with_capacity(num_entries);
    for _ in 0..num_entries {
      let key: i64 = rng.gen();
      let key = I64::from(key);
      let value: i64 = rng.gen();
      let value = I64::from(value);
      entries.push((key, value));
    }
    entries.sort_by_key(|&(k, _)| k);
    entries
  }

  /// Creates a leaf with pseudo-randomly generated data.
  pub fn random_leaf(
    lower_bound: i64,
    upper_bound: i64,
    num_tombstones: usize,
    num_entries: usize,
    seed: Option<[u8; 32]>,
  ) -> CLiMBTreeNodeGlyph<ArcGlyph, I64, I64> {
    let seed = seed.unwrap_or([42u8; 32]);
    let gen = RandomI64LeafGenerator {
      lower_bound,
      upper_bound,
      num_tombstones,
      num_entries,
      seed,
    };
    let glyph = glyph_new_arc(gen).unwrap();
    CLiMBTreeNodeGlyph::<_, I64, I64>::from_glyph(glyph).unwrap()
  }

  pub struct RandomI64LeafGenerator {
    pub lower_bound:    i64,
    pub upper_bound:    i64,
    pub num_tombstones: usize,
    pub num_entries:    usize,
    pub seed:           [u8; 32],
  }

  impl ToGlyph for RandomI64LeafGenerator {
    fn glyph_encode(
      &self,
      target: &mut [u8],
      cursor: &mut usize,
    ) -> Result<(), GlyphErr> {
      // We need to fill BTreeMap/Sets with them first, because the iterators
      // need to be in order
      let mut rng = ChaCha20Rng::from_seed(self.seed);
      let mut tombstones = BTreeSet::new();
      let mut entries = BTreeMap::new();

      for _ in 0..self.num_tombstones {
        let key: i64 = rng.gen_range(self.lower_bound..self.upper_bound);
        let key = I64::from(key);
        tombstones.insert(key);
      }
      for _ in 0..self.num_entries {
        let key: i64 = rng.gen_range(self.lower_bound..self.upper_bound);
        let value: i64 = rng.gen();
        entries.insert(I64::from(key), I64::from(value));
      }

      let mut writer = CLiMBTreeNodeWriter::<I64, I64>::new(
        target,
        cursor,
        0,
        0,
        self.num_tombstones,
        self.num_entries,
      )?;
      for tombstone in tombstones {
        writer.write_tombstone(&tombstone)?;
      }
      for (key, value) in entries {
        writer.write_entry(&key, &value)?;
      }
      writer.finish()
    }

    fn glyph_len(&self) -> usize {
      let mut len_calc = CLiMBTreeNodeLenCalc::<I64, I64>::new();
      len_calc.fixed_len_tombstones(self.num_tombstones);
      len_calc.fixed_len_entries(self.num_entries);
      len_calc.finish()
    }
  }

  #[test]
  fn climb_tree_codec() {
    //=== Set up Test Data ===/
    let mut rng = ChaCha20Rng::from_seed([42u8; 32]);
    let mut pivots = BTreeMap::new();
    let mut ss_tables = Vec::new();
    let tombstones = random_tombstones(&mut rng, 10);
    let entries = random_entries(&mut rng, 10);

    for _i in 0..10i64 {
      // Pivots, Children, and their SST Links.
      let (pivot, hash, sst_links) = random_pivot(&mut rng);
      pivots.insert(pivot, (hash, sst_links));

      let (target_hash, target_len, bf) = random_sst(&mut rng);
      ss_tables.push((target_hash, target_len, bf));
    }

    //=== Do Length Calculation Manually ===/
    // We're not going to test a `ToGlyph` encoder, we're going to test
    // CLiMBTreeNodeWriter.
    let mut lc = CLiMBTreeNodeLenCalc::<I64, I64>::new();
    for (pivot, (_target_hash, ss_tables)) in &pivots {
      let mut plc = lc.add_pivot(I64::length(pivot.as_ref()), true);
      for (_target_hash, _target_len, bf) in ss_tables {
        plc.add_ss_table(bf.data().len()).unwrap();
      }
      plc.finish()
    }
    for (_target_hash, _target_len, bf) in &ss_tables {
      lc.add_ss_table(bf.data().len());
    }
    lc.fixed_len_tombstones(tombstones.len());
    lc.fixed_len_entries(entries.len());
    let length = lc.finish();

    //=== Do Encoding Manually ===/
    let mut buffer = BoxGlyph::new_buffer(length).unwrap();
    let mut cursor = 0usize;
    let mut enc = CLiMBTreeNodeWriter::<I64, I64>::new(
      buffer.as_mut(),
      &mut cursor,
      pivots.len(),
      ss_tables.len(),
      tombstones.len(),
      entries.len(),
    )
    .unwrap();
    for (pivot, (target_hash, ss_tables)) in &pivots {
      let mut pw = enc
        .start_pivot(pivot.as_ref(), Some(target_hash), ss_tables.len())
        .unwrap();
      for (target_hash, target_len, bf) in ss_tables {
        pw.write_ss_table(target_hash, *target_len, &bf.borrow())
          .unwrap();
      }
      pw.finish();
    }
    for (target_hash, target_len, bf) in &ss_tables {
      enc
        .write_ss_table(target_hash, *target_len, bf.num_hashes(), bf.data())
        .unwrap();
    }
    for tombstone in &tombstones {
      enc.write_tombstone(&tombstone).unwrap();
    }
    for (key, value) in &entries {
      enc.write_entry(key.as_ref(), value.as_ref()).unwrap();
    }
    enc.finish().unwrap();
    dbg!(HexDump(buffer.as_ref()));

    //=== Glyph Decoding ===/
    let glyph = BoxGlyph::from_buffer(buffer).unwrap();
    let ctng = CLiMBTreeNodeGlyph::<_, I64, I64>::from_glyph(glyph).unwrap();
    dbg!(&ctng);

    //=== Data Verification ===/
    // Pivots

    // SSTables
    let ssti = ss_tables.iter();
    let gssti = ctng.iter_ss_tables();
    assert_eq!(ssti.len(), gssti.len());
    for ((target_hash, target_len, bf), info) in ssti.zip(gssti) {
      assert_eq!(target_hash, info.target_hash());
      assert_eq!(*target_len, info.target_length());
      assert_eq!(bf.num_hashes(), info.bloom_k());
      assert_eq!(bf.data(), info.bloom_data());
    }

    // Tombstones
    assert!(tombstones.iter().eq(ctng.iter_tombstones()));

    // Entries
    assert!(entries.iter().map(|(a, b)| (a, b)).eq(ctng.iter_entries()));

    //
    //
    // //== Encoding and Decoding without Error
    // let lw = CLiMBTreeNodeIterWriter::<I64, I64, _, _, _, _>::new(
    //   children.iter().map(|(lower_bound, target)| {
    //     (lower_bound, Some(target), iter::empty())
    //   }),
    //   tombstones.iter(),
    //   entries.iter(),
    // );
    // let calc_len = lw.glyph_len();
    // dbg!(calc_len);
    //
    // let glyph = glyph_new(lw).unwrap();
    // assert_eq!(calc_len, glyph.len());
    // dbg!(&glyph);
    // let decoded = CLiMBTreeNodeGlyph::<_, I64, I64>::from_glyph(glyph).unwrap();
    // dbg!(&decoded);
    //
    // //== Equality for pivot keys / bounds and targets and key bounds
    // let src_children = children.iter();
    // let decoded_children = decoded.iter_pivots();
    // assert_eq!(src_children.len(), 10);
    // assert_eq!(src_children.len(), decoded_children.len());
    // let mut last_upper_bound = None;
    // for (i, ((src_lower_bound, src_hash), pivot_info)) in
    //   src_children.zip(decoded_children).enumerate()
    // {
    //   if i == 0 {
    //     // Node doesn't return lower bound for the first pivot, and we'll
    //     // test for upper bound equality on the next iteration
    //     assert!(pivot_info.upper_bound().is_some());
    //     assert_eq!(src_hash, pivot_info.child_hash().unwrap());
    //     last_upper_bound = Some(pivot_info.upper_bound().unwrap());
    //   } else if i < 9 {
    //     let lower_bound = pivot_info.lower_bound();
    //     // Lower bound matches source data
    //     assert_eq!(src_lower_bound, lower_bound);
    //     // Last node's upper bound is equal to this one's lower bound
    //     assert_eq!(last_upper_bound.unwrap(), pivot_info.lower_bound());
    //     // Target node hash matches source data
    //     assert_eq!(src_hash, pivot_info.child_hash().unwrap());
    //     // Replace last node's upper bound for next round
    //     last_upper_bound = Some(pivot_info.upper_bound().unwrap());
    //   } else {
    //     // Last node is similar to others, except there's no upper bound
    //     assert_eq!(pivot_info.lower_bound(), last_upper_bound.unwrap());
    //     assert_eq!(src_hash, pivot_info.child_hash().unwrap());
    //     assert!(pivot_info.upper_bound().is_none());
    //   }
    // }
    //
    // //== Equality for tombstones and entries
    // let src_tombstones = tombstones.iter();
    // let decoded_tombstones = decoded.iter_tombstones();
    // assert_eq!(src_tombstones.len(), decoded_tombstones.len());
    // for (src, decoded) in src_tombstones.zip(decoded_tombstones) {
    //   assert_eq!(src, decoded);
    // }
    // let src_entries = entries.iter();
    // let decoded_entries = decoded.iter_entries();
    // assert_eq!(src_entries.len(), decoded_entries.len());
    // for (src, decoded) in src_entries.zip(decoded_entries) {
    //   assert_eq!(src, decoded);
    // }
  }
}
