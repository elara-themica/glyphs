use std::collections::BTreeMap;
use std::iter;
use std::time::Duration;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion, Throughput};
use criterion::measurement::WallTime;
use glyphs::{FromGlyph, Glyph, GlyphErr, ToGlyph};
use glyphs::collections::{BasicVecGlyph, MapGlyph, VecGlyph, VecGlyphWriter};
use glyphs::structured::{DocGlyph, Document};

pub const TEST_PLAINTEXT: &str =
  "Deutsche truppen sind jetzt in England.";

pub fn codec(c: &mut Criterion) {
  // Use a static buffer, so we're not just benchmarking allocation.
  let mut buffer = [0u8; 8192];
  let mut group = c.benchmark_group("codec");

  // These are reasonable parameters, given how quick / small these functions
  // are.
  group.warm_up_time(Duration::from_millis(10));
  group.measurement_time(Duration::from_millis(250));

  //=== u32 ===//
  42u32.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.throughput(Throughput::Bytes(42u32.glyph_len() as u64));
  group.bench_function("encode_u32", |b| b.iter(
    || 42u32.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  group.bench_function("decode_u32", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = u32::from_glyph(glyph).unwrap();
    }
  ));

  //=== char ===//
  '🦋'.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.throughput(Throughput::Bytes('🦋'.glyph_len() as u64));
  group.bench_function("encode_char", |b| b.iter(
    || '🦋'.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  group.bench_function("decode_char", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = char::from_glyph(glyph).unwrap();
    }
  ));

  //=== u64 ===//
  42u64.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.throughput(Throughput::Bytes(42u64.glyph_len() as u64));
  group.bench_function("encode_u64", |b| b.iter(
    || 42u64.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  group.bench_function("decode_u64", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = u64::from_glyph(glyph).unwrap();
    }
  ));

  //=== str ===//
  TEST_PLAINTEXT.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.throughput(Throughput::Bytes(TEST_PLAINTEXT.glyph_len() as u64));
  group.bench_function("encode_str", |b| b.iter(
    || TEST_PLAINTEXT.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  group.bench_function("decode_str", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = <&str>::from_glyph(glyph).unwrap();
    }
  ));


  //=== Vector Glyphs ===//
  let mut number_glyphs = Vec::new();
  for i in 0..32u64 {
    let glyph = Glyph::new(i).unwrap();
    number_glyphs.push(glyph);
  }
  group.throughput(Throughput::Bytes(VecGlyphWriter::from_slice(&number_glyphs[..]).glyph_len() as u64));
  group.bench_function("encode_vec", |b| b.iter(
    || VecGlyphWriter::from_slice(&number_glyphs[..]).glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  VecGlyphWriter::from_slice(&number_glyphs[..]).glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.bench_function("decode_vec", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = VecGlyph::from_glyph(glyph).unwrap();
    }
  ));


  //=== Map Glyphs == //
  let mut names = BTreeMap::new();
  names.insert("Ashley", "Williams");
  names.insert("Garrus", "Vakarian");
  names.insert("Jane", "Shepard");
  names.insert("Kaiden", "Alenko");
  names.insert("Liara", "T'Soni");
  names.insert("Tali", "Vas Normandy");
  names.insert("Wrex", "Urdnot");

  group.throughput(Throughput::Bytes(names.glyph_len() as u64));
  group.bench_function("encode_map", |b| b.iter(
    || names.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  names.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.bench_function("decode_map", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = MapGlyph::from_glyph(glyph).unwrap();
    }
  ));

  //=== Basic Vector Glyphs ===//
  let mut numbers = Vec::new();
  for i in 0..32u64 {
    numbers.push(i);
  }
  group.throughput(Throughput::Bytes(numbers[..].glyph_len() as u64));
  group.bench_function("encode_basic_vec", |b| b.iter(
    || numbers.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  numbers.glyph_encode(&mut buffer[..], &mut 0).unwrap();
  group.bench_function("decode_basic_vec", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = BasicVecGlyph::from_glyph(glyph).unwrap();
    }
  ));

  //=== Document Glyphs ===/
  let doc = Document::new((),());
  doc.glyph_encode(&mut buffer[..], &mut 0).unwrap();

  group.throughput(Throughput::Bytes(doc.glyph_len() as u64));
  group.bench_function("encode_doc", |b| b.iter(
    || doc.glyph_encode(&mut buffer[..], &mut 0).unwrap()
  ));
  group.bench_function("decode_doc", |b| b.iter(
    || {
      let glyph = Glyph::read(&buffer[..], &mut 0).unwrap();
      let _value = DocGlyph::from_glyph(glyph).unwrap();
    }
  ));
}


criterion_group!(benches, codec);
criterion_main!(benches);