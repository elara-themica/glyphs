use glyphs::{glyph_new_arc, Glyph};

#[test]
fn arc_glyph() {
  let glyph = glyph_new_arc(()).unwrap();
  dbg!(&glyph);
  assert_eq!(glyph.len(), 8);

  let g1 = glyph.clone();
  let g2 = glyph.clone();
  let g3 = glyph.clone();

  assert_eq!(g1.as_ref(), g2.as_ref());
  assert_eq!(g1.as_ref().as_ptr(), g3.as_ref().as_ptr());
  dbg!(glyph.strong_count());
  dbg!(glyph);
  dbg!(&g1);
  dbg!(g1.strong_count());
}
