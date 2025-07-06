use crate::{
  crypto::{
    CryptographicHash, GlyphHash, HashContext, Sha256Context, Sha256Hash,
    Sha3Hash,
  },
  glyph::glyph_close,
  util::debug::ShortHexDump,
  zerocopy::{pad_to_word, round_to_word, ZeroCopy, U128, U16},
  BoxGlyphBuf, FromGlyph, FromGlyphErr, Glyph, GlyphErr, GlyphHeader,
  GlyphType, ToGlyph, UnsafeGlyph,
};
use core::fmt::{Debug, Formatter};
use ed25519_dalek::{Digest, Signature, SigningKey, VerifyingKey};

/// Allows creation of a [`SignatureGlyph`] for cryptographic signatures.
///

///
/// A structure for creating cryptographic signature glyphs.
///
/// This struct allows for the creation of a `SignatureGlyph` using a cryptographic key and
/// additional fields such as the signed hash, optionally a signing statement, and other metadata.
///
/// # Example
///
/// ```rust
/// use glyphs::crypto::{GlyphHash, GlyphSigner, CryptoKeyGlyph, CryptographicHash, Sha3Hash};
///
/// // Example signing key (generated for demonstration purposes)
/// let signing_key = CryptoKeyGlyph::gen_ed25519_private(&mut rand::thread_rng(), None, None).unwrap();
/// println!("Generated a signing key with fingerprint {}", signing_key.key_fingerprint());
/// let signer = signing_key.signer().unwrap();
///
/// // The hash to be signed
/// let glyph_hash = GlyphHash::new(b"example data to sign");
///
/// // Optionally include a statement and define work iterations
/// let statement = None;
/// let work_iterations = 1000;
///
/// // Perform the signing operation
/// let signature = signer.sign(glyph_hash, statement, work_iterations).unwrap();
///
/// // Use the signature for further proof or verification
/// match signature.valid_for() {
///   None => println!("Signature is Invalid"),
///   Some(fingerprint) => println!("Signature is valid for key with fingerprint {}", &fingerprint),
/// }
/// ```
pub struct GlyphSigner {
  key: SigningKey,
}

impl GlyphSigner {
  /// Simple constructor
  pub(super) fn new(key: SigningKey) -> Self {
    Self { key }
  }

  /// Creates a new [`SignatureGlyph`]
  pub fn sign(
    &self,
    what: GlyphHash,
    statement: Option<BoxGlyph>,
    work_iterations: u64,
  ) -> Result<SignatureGlyph<BoxGlyph>, GlyphErr> {
    // The first thing we need to do is the proof of work, since the signature
    // will also be over this.
    let mut base_work_hash = Sha256Context::new();
    base_work_hash.update(what.as_ref());
    if let Some(statement) = &statement {
      base_work_hash.update(statement.as_ref());
    }

    let work_iterations = work_iterations as u128;
    let mut first_hash = base_work_hash.clone();
    first_hash.update(&(0u128.to_le_bytes())[..]);
    let mut low_hash = first_hash.finish();
    let mut low_i = 0;
    for i in 1..work_iterations {
      let mut work_hash = base_work_hash.clone();
      work_hash.update(&(i.to_le_bytes())[..]);
      let work_hash = work_hash.finish();
      if work_hash < low_hash {
        low_i = i;
        low_hash = work_hash;
      }
    }

    // Now we need to calculate the signature
    let mut signature_hash = ed25519_dalek::Sha512::new();
    signature_hash.update(low_i.to_le_bytes());
    signature_hash.update(what.as_ref());
    if let Some(statement) = &statement {
      signature_hash.update(statement.as_ref());
    }
    let sig = self
      .key
      .sign_prehashed(signature_hash, None)
      .map_err(|_err| GlyphErr::SignatureInvalid)?;
    let sig_bytes = sig.to_bytes();
    let key_bytes = self.key.verifying_key().to_bytes();

    let statement_len = match &statement {
      None => 0,
      Some(glyph) => glyph.len(),
    };
    let glyph_len =
      signature_glyph_len_calc(SignatureGlyphTypes::Ed25519, statement_len);
    let mut buf = BoxGlyphBuf::new(glyph_len)?;
    signature_glyph_writer(
      buf.as_mut(),
      &mut 0,
      SignatureGlyphTypes::Ed25519,
      low_i,
      &what,
      statement.as_ref().map(|b| b.borrow()),
      &sig_bytes[..],
      &key_bytes[..],
    )?;
    let glyph = buf.finalize()?;
    let sig_glyph = SignatureGlyph::from_glyph(glyph)?;
    Ok(sig_glyph)
  }
}

/// The zero-copy header for signature glyphs
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct SignatureGlyphHeader {
  version:     u8,
  flags:       u8,
  sig_type:    U16,
  sig_len:     U16,
  pk_len:      U16,
  work_proof:  U128,
  what_signed: GlyphHash,
}

impl SignatureGlyphHeader {
  /// The associated signature glyph contains a signing statement.
  pub const FLAG_HAS_STATEMENT: u8 = 0b0000_0001;

  pub fn has_statement(&self) -> bool {
    self.flags & Self::FLAG_HAS_STATEMENT != 0
  }

  pub fn sig_len(&self) -> usize {
    self.sig_len.get() as usize
  }

  pub fn pk_len(&self) -> usize {
    self.pk_len.get() as usize
  }

  pub fn work_proof(&self) -> u128 {
    self.work_proof.into()
  }

  pub fn what_signed(&self) -> &GlyphHash {
    &self.what_signed
  }

  pub fn sig_type(&self) -> SignatureGlyphTypes {
    self.sig_type.get().into()
  }
}

unsafe impl ZeroCopy for SignatureGlyphHeader {}

/// A self-proving cryptographic signature, with metadata and proof-of-work.
pub struct SignatureGlyph<G: Deref<Target = Glyph>> {
  glyph:      G,
  header:     *const SignatureGlyphHeader,
  statement:  Option<UnsafeGlyph>,
  public_key: *const u8,
  signature:  *const u8,
  work_proof: Sha256Hash,
  valid_for:  Option<Sha3Hash>,
}

impl<G: Deref<Target = Glyph>> SignatureGlyph<G> {
  fn header(&self) -> &SignatureGlyphHeader {
    // SAFETY: Checked when decoded, pointers used b/c/o internal self-reference
    unsafe { &*self.header }
  }

  /// Returns the type of cryptographic signature used.
  pub fn sig_type(&self) -> SignatureGlyphTypes {
    self.header().sig_type().into()
  }

  /// Returns the raw bytes of the serialized cryptographic signature.
  pub fn sig_bytes(&self) -> &[u8] {
    // SAFETY: Checked when decoded, pointers used b/c/o internal self-reference
    unsafe {
      core::slice::from_raw_parts(
        self.signature,
        self.header().sig_len().into(),
      )
    }
  }

  /// Returns the raw bytes of the serialized public key.
  pub fn pk_bytes(&self) -> &[u8] {
    // SAFETY: Checked when decoded, pointers used b/c/o internal self-reference
    unsafe {
      core::slice::from_raw_parts(
        self.public_key,
        self.header().pk_len().into(),
      )
    }
  }

  /// Returns `true` if the signature is valid.
  pub fn valid_for(&self) -> Option<&Sha3Hash> {
    self.valid_for.as_ref()
  }

  /// Returns the result of the proof-of-work calculation.
  pub fn work_proof(&self) -> &Sha256Hash {
    &self.work_proof
  }

  /// Returns the hash of what was signed.
  pub fn what_signed(&self) -> &GlyphHash {
    self.header().what_signed()
  }

  /// Returns the signing statement made in this signature, if any.
  pub fn statement(&self) -> Option<&Glyph> {
    // SAFETY: Checked when decoded, pointers used b/c/o internal self-reference
    self.statement.map(|ug| unsafe { ug.into_parsed() })
  }
}

impl<G: Deref<Target = Glyph>> FromGlyph<G> for SignatureGlyph<G> {
  fn from_glyph(glyph: G) -> Result<Self, FromGlyphErr<G>> {
    if let Err(e) = glyph.header().confirm_type(GlyphType::Signature) {
      return Err(FromGlyphErr::new(glyph, e));
    }
    let content = glyph.content_padded();
    let mut cursor = 0;
    let header = match SignatureGlyphHeader::bbrf(content, &mut cursor) {
      Ok(header) => header,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };
    let statement =
      if header.flags & SignatureGlyphHeader::FLAG_HAS_STATEMENT != 0 {
        match Glyph::read(content, &mut cursor) {
          Ok(glyph) => Some(glyph),
          Err(e) => return Err(FromGlyphErr::new(glyph, e)),
        }
      } else {
        None
      };
    let signature = match u8::bbrfs(content, &mut cursor, header.sig_len()) {
      Ok(bytes) => bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };
    let public_key = match u8::bbrfs(content, &mut cursor, header.pk_len()) {
      Ok(bytes) => bytes,
      Err(e) => return Err(FromGlyphErr::new(glyph, e)),
    };

    let mut work_proof = Sha256Context::new();
    work_proof.update(header.what_signed.as_ref());
    if let Some(statement) = statement {
      work_proof.update(statement.as_ref());
    }
    work_proof.update(header.work_proof.bytes());
    let work_proof = work_proof.finish();

    let valid_for = verify_signature(header, statement, public_key, signature);

    let header = header as *const SignatureGlyphHeader;
    // SAFETY: We're committing that we won't leak this into unsafe code.
    let statement = statement.map(|s| unsafe { UnsafeGlyph::from_parsed(s) });
    let public_key = public_key.as_ptr();
    let signature = signature.as_ptr();

    Ok(Self {
      glyph,
      header,
      statement,
      public_key,
      signature,
      work_proof,
      valid_for,
    })
  }
}

impl<G: Deref<Target = Glyph>> Debug for SignatureGlyph<G> {
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
    let mut df = f.debug_struct("SignatureGlyph");
    df.field("sig_type", &self.sig_type());
    df.field("what_signed", &self.what_signed());
    df.field("signature", &ShortHexDump(&self.sig_bytes(), 0));
    df.field("public_key", &ShortHexDump(&self.pk_bytes(), 0));
    if let Some(statement) = self.statement() {
      df.field("statement", &statement);
    }
    df.field("work_proof", &self.work_proof());
    match self.valid_for() {
      None => {
        df.field("valid_for", &Option::<&Sha3Hash>::None);
      },
      Some(fingerprint) => {
        df.field("valid_for", fingerprint);
      },
    }
    df.finish()
  }
}

fn verify_signature(
  header: &SignatureGlyphHeader, // has nonce and signed
  statement: Option<ParsedGlyph>,
  key_bytes: &[u8],
  sig_bytes: &[u8],
) -> Option<Sha3Hash> {
  match header.sig_type() {
    SignatureGlyphTypes::Ed25519 => {
      let key_bytes: &[u8; 32] = match u8::bbrfa(key_bytes, &mut 0) {
        Ok(key_bytes) => key_bytes,
        Err(_) => return None,
      };
      let sig_bytes: &[u8; 64] = match u8::bbrfa(sig_bytes, &mut 0) {
        Ok(sig_bytes) => sig_bytes,
        Err(_) => return None,
      };
      let key = match VerifyingKey::from_bytes(key_bytes) {
        Ok(key) => key,
        Err(_) => return None,
      };
      let sig = Signature::from_bytes(sig_bytes);

      let mut signature_hash = ed25519_dalek::Sha512::new();
      signature_hash.update(header.work_proof().to_le_bytes());
      signature_hash.update(header.what_signed.as_ref());
      if let Some(statement) = statement {
        signature_hash.update(statement.as_ref());
      }

      match key.verify_prehashed_strict(signature_hash, None, &sig) {
        Ok(()) => {
          let fingerprint = Sha3Hash::new(&key_bytes[..]);
          Some(fingerprint)
        },
        Err(_) => None,
      }
    },
    SignatureGlyphTypes::Unknown => None,
  }
}

pub(crate) fn signature_glyph_writer(
  target: &mut [u8],
  cursor: &mut usize,
  sig_type: SignatureGlyphTypes,
  work_proof: u128,
  what_signed: &GlyphHash,
  statement: Option<ParsedGlyph>,
  signature: &[u8],
  public_key: &[u8],
) -> Result<(), GlyphErr> {
  let glyph_offset = *cursor;
  *cursor += size_of::<GlyphHeader>();

  let mut flags: u8 = 0;
  if statement.is_some() {
    flags |= SignatureGlyphHeader::FLAG_HAS_STATEMENT;
  }
  let sig_len = U16::try_from(signature.len())
    .map_err(|_err| GlyphErr::SignatureLengthOverflow(signature.len()))?;
  let pk_len = U16::try_from(public_key.len())
    .map_err(|_err| GlyphErr::SignatureKeyLengthOverflow(public_key.len()))?;

  SignatureGlyphHeader {
    version: 0,
    flags,
    sig_type: sig_type.into(),
    sig_len,
    pk_len,
    work_proof: work_proof.into(),
    what_signed: *what_signed,
  }
  .bbwr(target, cursor)?;
  if let Some(statement) = statement {
    statement.glyph_encode(target, cursor)?;
  }
  u8::bbwrs(signature, target, cursor)?;
  pad_to_word(target, cursor)?;
  u8::bbwrs(public_key, target, cursor)?;
  pad_to_word(target, cursor)?;

  glyph_close(GlyphType::Signature, target, glyph_offset, cursor, false)
}

/// Returns the number of bytes necessary to write a signature glyph.
pub(crate) fn signature_glyph_len_calc(
  sig_type: SignatureGlyphTypes,
  statement_length: usize,
) -> usize {
  let mut len = size_of::<GlyphHeader>();
  len += size_of::<SignatureGlyphHeader>();
  len += statement_length;
  len += round_to_word(sig_type.pk_len());
  len += round_to_word(sig_type.sig_len());
  len
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::crypto::CryptoKeyGlyph;
  use rand::SeedableRng;
  use rand_chacha::ChaChaRng;

  #[test]
  fn signatures() {
    let mut rng = ChaChaRng::from_seed([0; 32]);
    let key =
      CryptoKeyGlyph::gen_ed25519_private(&mut rng, None, None).unwrap();
    std::dbg!(&key);
    let key_fingerprint = key.key_fingerprint();
    let signer = key.signer().unwrap();
    let sig = signer.sign(GlyphHash::default(), None, 10000).unwrap();
    std::dbg!(&sig);
    assert_eq!(sig.valid_for().unwrap(), key_fingerprint);
    // TODO: Test the negative.
  }
}
