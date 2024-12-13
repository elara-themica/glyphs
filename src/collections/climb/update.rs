use crate::{
  collections::climb::{
    CLiMBTreeKey, CLiMBTreeNodeGlyph, CLiMBTreeValue, UpdateContext,
  },
  ArcGlyph, GlyphErr,
};
use alloc::boxed::Box;
use async_recursion::async_recursion;

pub struct CLiMBTreeUpdateConfig {
  max_leaf_node_length:   usize,
  updates_in_nodes:       bool,
  old_nodes_as_ss_tables: bool,
}

pub enum NodeUpdateResult<K, V>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  TooSmall, // One node, notifies parent we're under the minimum threshold.
  Updated(CLiMBTreeNodeGlyph<ArcGlyph, K, V>), // One node, allows 1:1 replacement
  Split,                                       // Several nodes
}

#[async_recursion]
pub async fn update_node<K, V>(
  config: CLiMBTreeUpdateConfig,
  node: CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
  mut context: UpdateContext<K, V>,
  _depth: usize,
) -> Result<NodeUpdateResult<K, V>, GlyphErr>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  /* === Step 1: If possible, update node-level write caches ===

     1.1: If the updates can fit into an updated version of this node itself, do that.
     1.2: If we can do that without including existing node data, do that.  We'll use the old
          version of this node as an SSTable write cache, so we'll need to take that into account.
     1.3: If data still won't fit, then can we write entire new nodes as SSTables?
  */

  let (tombstones_len, entries_len) = context.get_encode_length();
  let space_needed = tombstones_len + entries_len;

  // 1.1: Update this node if possible.
  let simple_rewrite_space = config.max_leaf_node_length - node.glyph_len();
  if space_needed < simple_rewrite_space {
    context.add_older_node(&node)?;
    // let writer = ReplaceDataNodeWriter::new(&node, &context);
    // let glyph = glyph_new_arc(writer)?;
    // let node = CLiMBTreeNodeGlyph::<_, K, V>::from_glyph(glyph)?;
    // return Ok(NodeUpdateResult::Updated(node));
    todo!("FIXME")
  }

  /* === Step 2: Flush data to children. ===

     2.1: We need to load all the data from existing nodes.
     2.2: Split the update set across the existing pivots.
     2.3: Apply the update algorithm to each pivot
     2.4: Merge / re-balance children that are undersized.
  */

  /* === Step 3: Update This Node ===

    3.1: Evaluate whether we (a) need to split or (b) are below the minimum threshold.
    3.2: Serialize new node(s) and return them to the parent.
  */

  todo!()
}

pub fn merge_nodes<K, V>(
  _first: CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
  _second: CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
) -> Result<NodeUpdateResult<K, V>, GlyphErr>
where
  K: CLiMBTreeKey,
  V: CLiMBTreeValue,
{
  todo!()
}

// /// Creates a new leaf node.
// ///
// ///
// ///
// pub fn update_leaf<K: CLiMBTreeKey, V: CLiMBTreeValue>(
//   node: CLiMBTreeNodeGlyph<ArcGlyph, K, V>,
//   mut context: UpdateContext<K, V>,
//   parameters: CLiMBTreeUpdateConfig,
// ) -> Result<(), GlyphErr> {
//   // Make sure all data has been added, but then we can drop tombstones, as
//   // we'll be writing a leaf.
//   context.add_older_node(&node)?;
//   context.drop_tombstones();
//
//   // See if it fits in one node.
//   let total_writer = UpdateContextLeafWriter::new(&context);
//   let total_len = total_writer.glyph_len();
//   if total_len < parameters.max_leaf_node_length {
//     // If it does, write that node and return the result.
//     let glyph = glyph_new_arc(total_writer)?;
//     let node = CLiMBTreeNodeGlyph::<_, K, V>::from_glyph(glyph)?;
//     // TODO: Return a single node
//   }
//   // If it doesn't, split it into parts that fit and write those.
//   let mut splits = alloc::vec::Vec::new();
//   let max_data = parameters.max_leaf_node_length
//     - size_of::<GlyphHeader>()
//     - size_of::<CLiMBTreeNodeHeader>()
//     - size_of::<GlyphOffset>(); // Potential offsets padding.
//   while let Some(split) = context.split_at_enc_bytes(max_data) {
//     let writer = UpdateContextLeafWriter::new(&split);
//     let node = glyph_new_arc(writer)?;
//     let node = CLiMBTreeNodeGlyph::<_, K, V>::from_glyph(node)?;
//     splits.push(node);
//   }
//   // What's left should fit.
//   let writer = UpdateContextLeafWriter::new(&context);
//
//   // TODO: What if it's below some minimum size?
//   // Probably, handle that beforehand.
//
//   todo!()
// }

/// Reads data from existing nodes into an update context, i.e., to flush the write cache.
///
/// Tree updates will be read from the _data sections_ of these nodes only.  No references will be
/// consulted or fetched.
///
/// Parameters:
///
/// - `context`: the new data for this update.
/// - `nodes`: An iterator of the nodes to add, from newest to oldest.
pub(super) fn read_leaf_data<'a, K: CLiMBTreeKey, V: CLiMBTreeValue>(
  context: &mut UpdateContext<K, V>,
  nodes: impl Iterator<Item = &'a CLiMBTreeNodeGlyph<ArcGlyph, K, V>>,
) -> Result<(), GlyphErr> {
  for node in nodes {
    context.add_older_node(node)?;
  }
  Ok(())
}

#[allow(unused)]
#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn climb_tree_update() {
    todo!()
  }
}
