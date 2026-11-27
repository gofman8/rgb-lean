import Rgb.Ops.Consignment
import Rgb.Lib.Enums
import Rgb.Lib.Error

/-!
# Proxy cryptography

The client-side cryptography of the RGB proxy protocol 1.0 (`encryption.rs`): operation keys and
their signatures, the keys the two parties of a transfer derive, the proxy identifiers, the
encryption of the payloads a proxy stores and the proof of work that guards `consignment.post`.

The model is symbolic:

* `sha256` is a computable stand-in for SHA-256 with its form (32 bytes, shown as 64 lowercase hex
  digits), so identifiers have the shape the protocol gives them. The model assumes it free of
  collisions, as the protocol assumes of SHA-256.
* A key is named by its seed; its public key is the hash of that name. A signature records its
  signer's public key and the hash of the message, so it verifies exactly for that key and message.
* The secret two parties share is a hash of their two public keys taken in order, so
  `deriveShared a b.pk = deriveShared b a.pk` by construction. Secrecy is assumed and not
  modelled.
* An encrypted blob keeps its payload and the key and plaintext hash it is sealed with. It opens
  exactly with that key and hash; any other bytes fail with the error `decrypt_stream` gives them.
-/

namespace Rgb.Lib.ProxyCrypto

/-! ## Constants -/

/-- Encryption format version, the first byte of every encrypted blob (`ENC_VERSION`). -/
def encVersion : UInt8 := 0x01
/-- Plaintext bytes sealed per chunk (`CHUNK`, 64 KiB). -/
def chunkSize : Nat := 65536
/-- XChaCha20-Poly1305 tag bytes added to each chunk (`TAG`). -/
def tagLen : Nat := 16
/-- Bytes of a sealed full chunk (`ENC_CHUNK`). -/
def encChunkSize : Nat := chunkSize + tagLen
/-- HKDF label of the symmetric key (`INFO_ENC`). -/
def infoEnc : String := "rgb-proxy-server/enc/v1"
/-- HKDF label of the media-id key (`INFO_MEDIA_ID`). -/
def infoMediaId : String := "rgb-proxy-server/enc/v1/media-id"
/-- HKDF label of the witness seal blinding (`INFO_SEAL_BLINDING`). -/
def infoSealBlinding : String := "rgb-proxy-server/enc/v1/seal-blinding"
/-- Domain prefix of invoice ids (`INVOICE_ID_PREFIX`). -/
def invoiceIdPrefix : String := "rgb-proxy-server/invoice/v1"
/-- Domain prefix of transfer ids (`TRANSFER_ID_PREFIX`). -/
def transferIdPrefix : String := "rgb-proxy-server/transfer/v1"

/-! ## Hash -/

/-- One 64-bit lane of the stand-in hash: FNV-1a from a seeded basis, then the murmur3 mix. -/
private def lane (seed : UInt64) (s : String) : UInt64 :=
  let h := s.foldl (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211)
    (14695981039346656037 ^^^ seed)
  let h := (h ^^^ (h >>> 33)) * 0xff51afd7ed558ccd
  let h := (h ^^^ (h >>> 33)) * 0xc4ceb9fe1a85ec53
  h ^^^ (h >>> 33)

/-- Big-endian bytes of a lane. -/
private def laneBytes (h : UInt64) : Bytes :=
  (List.range 8).map fun i => (h >>> (8 * (7 - i)).toUInt64).toUInt8

/-- The stand-in for SHA-256 of the UTF-8 text `s`: four seeded lanes, 32 bytes. -/
def sha256 (s : String) : Bytes :=
  [1, 2, 3, 4].flatMap fun i => laneBytes (lane (0x9e3779b97f4a7c15 * i) s)

/-- Lowercase hex digit of a nibble. -/
private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lowercase hex of bytes (`hex::encode`). -/
def hex (b : Bytes) : String :=
  String.ofList (b.flatMap fun x => [hexChar (x.toNat / 16), hexChar (x.toNat % 16)])

/-- Hex SHA-256 of `s`: how the protocol writes every hash and id. -/
def sha256Hex (s : String) : String := hex (sha256 s)

/-- A lowercase hex digit. -/
def isLowerHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Text `hex::decode` accepts: an even number of hex digits of either case. -/
def isHex (s : String) : Bool :=
  s.length % 2 == 0 && s.all fun c => isLowerHexDigit c || ('A' ≤ c && c ≤ 'F')

/-! ## Operation keys and signatures -/

/-- An Ed25519 operation key, named by its 32-byte seed (`SigningKey::from_bytes`). -/
structure SecretKey where
  seed : String
  deriving DecidableEq, Repr, Inhabited

/-- Hex of the key's public key, as the protocol exchanges it. -/
def SecretKey.pk (sk : SecretKey) : String := sha256Hex ("ed25519/public/" ++ sk.seed)

/-- Hex that decodes to 32 bytes, the length `verifying_key_from_bytes` requires; every such key
is a valid point in the model. -/
def isPubkeyHex (s : String) : Bool := isHex s && s.length == 64

/-- An Ed25519 signature: the signer's public key and the hash of the signed message. -/
structure Ed25519Sig where
  signer : String
  digest : String
  deriving DecidableEq, Repr, Inhabited

/-- `sign_ed25519(sk, H(message))`: every proxy call signs the hash of its message. -/
def signMessage (sk : SecretKey) (message : String) : Ed25519Sig := ⟨sk.pk, sha256Hex message⟩

/-- `verify_ed25519(pk, H(message), sig)`. -/
def verifyMessage (pk message : String) (sig : Ed25519Sig) : Bool :=
  sig.signer == pk && sig.digest == sha256Hex message

/-! ## Shared keys -/

/-- Keys a sender and a recipient derive from their operation keys (`DerivedKeys`). -/
structure DerivedKeys where
  /-- XChaCha20-Poly1305 key of the consignment, the media and the signed transaction (hex). -/
  symKey : String
  /-- HMAC key of the media ids (hex). -/
  kmid : String
  /-- Blinding of the recipient's witness seal. -/
  sealBlinding : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- X25519 of one party's secret with the other's public key, as a hash of both public keys in
order. -/
def sharedSecret (ownPk theirPk : String) : String :=
  let (a, b) := if compare ownPk theirPk == .gt then (theirPk, ownPk) else (ownPk, theirPk)
  sha256Hex ("x25519/" ++ a ++ b)

/-- HKDF-SHA256 with no salt: the first `n` bytes expanded from `ikm` under `info`. -/
def hkdfExpand (ikm info : String) (n : Nat) : Bytes :=
  (sha256 ("hkdf-sha256/" ++ ikm ++ "/" ++ info)).take n

/-- `derive_shared(own_sk, their_pk)`: symmetric in the two parties. -/
def deriveShared (own : SecretKey) (theirPk : String) : DerivedKeys :=
  let ikm := sharedSecret own.pk theirPk
  { symKey := hex (hkdfExpand ikm infoEnc 32)
    kmid := hex (hkdfExpand ikm infoMediaId 32)
    sealBlinding := (Bytes.leValue (hkdfExpand ikm infoSealBlinding 8)).toUInt64 }

/-- The shared secret does not depend on which party computes it. -/
theorem sharedSecret_comm (x y : String) : sharedSecret x y = sharedSecret y x := by
  by_cases hxy : x = y
  · rw [hxy]
  · unfold sharedSecret
    have hs : compare y x = (compare x y).swap := Std.OrientedCmp.eq_swap
    cases h : compare x y with
    | lt => simp [hs, h, Ordering.swap]
    | eq => exact absurd (Std.LawfulEqCmp.eq_of_compare h) hxy
    | gt => simp [hs, h, Ordering.swap]

/-- A sender and a recipient derive the same keys and seal blinding. -/
theorem deriveShared_symm (a b : SecretKey) : deriveShared a b.pk = deriveShared b a.pk := by
  unfold deriveShared
  rw [sharedSecret_comm]

/-- `media_id`: hex HMAC-SHA256 of a media's hex digest under the media-id key. -/
def DerivedKeys.mediaId (k : DerivedKeys) (digestHex : String) : String :=
  sha256Hex ("hmac-sha256/" ++ k.kmid ++ "/" ++ digestHex)

/-! ## Identifiers -/

/-- `invoice_id`: hex `H(prefix ‖ beneficiary ‖ recipient_pk_hex)`, the beneficiary being the
recipient id string. -/
def invoiceId (beneficiary recipientPkHex : String) : String :=
  sha256Hex (invoiceIdPrefix ++ beneficiary ++ recipientPkHex)

/-- `transfer_id`: hex `H(prefix ‖ invoice_id ‖ sender_pk_hex)`. -/
def transferId (invoiceId senderPkHex : String) : String :=
  sha256Hex (transferIdPrefix ++ invoiceId ++ senderPkHex)

/-- `is_transfer_id`: 64 lowercase hex digits, the form of a hex SHA-256. -/
def isTransferId (s : String) : Bool := s.length == 64 && s.all isLowerHexDigit

/-! ## Payloads and blobs -/

/-- The plaintext of a file exchanged through a proxy. -/
inductive Payload where
  /-- A consignment file. -/
  | consignment (c : Consignment)
  /-- A consensus-serialized transaction. -/
  | tx (t : Tx)
  /-- Any other bytes: a media file, or bytes that are not what the receiver expects. -/
  | bytes (data : String)
  deriving DecidableEq, Repr, Inhabited

namespace Payload

/-- The model's bytes of the file: a stand-in for its encoding with the same first byte (a
consignment file starts with `RGB\0` and its type magic, a transaction with its version). -/
def render : Payload → String
  | .consignment c => "RGB\x00" ++ (if c.transfer then "TFR" else "CON") ++ reprStr c
  | .tx t => String.ofList ((Bytes.le t.version.toNat 4).map fun b => Char.ofNat b.toNat)
      ++ encode t
  | .bytes d => d

/-- File size in bytes. -/
def len (p : Payload) : Nat := p.render.utf8ByteSize

/-- First byte of the file, if any. -/
def firstByte? : Payload → Option UInt8
  | .consignment _ => some 0x52
  | .tx t => some t.version.toUInt8
  | .bytes d => (Bytes.ofString d).head?

/-- Hex SHA-256 of the file: `consignment_hash`, `signed_tx_hash` or a media digest. -/
def hash (p : Payload) : String := sha256Hex p.render

/-- The consignment of a consignment file. -/
def consignment? : Payload → Option Consignment
  | .consignment c => some c
  | _ => none

/-- The transaction of a transaction file. -/
def tx? : Payload → Option Tx
  | .tx t => some t
  | _ => none

end Payload

/-- Chunks `encrypt_stream` seals for `len` plaintext bytes: `max(1, ceil(len / CHUNK))`. -/
def chunkCount (len : Nat) : Nat := max 1 ((len + chunkSize - 1) / chunkSize)

/-- Bytes of the blob sealing `len` plaintext bytes: the version byte and a tag per chunk. -/
def sealedLen (len : Nat) : Nat := 1 + len + tagLen * chunkCount len

/-- What `encrypt_blob` makes of a payload. -/
structure Sealed where
  /-- First byte of the blob. -/
  version : UInt8 := encVersion
  /-- Symmetric key the chunks are sealed with. -/
  key : String
  /-- Hex SHA-256 of the plaintext the sender gave, whose tail is the nonce base. -/
  plainHash : String
  payload : Payload
  deriving DecidableEq, Repr, Inhabited

namespace Sealed

/-- Bytes of the blob. -/
def len (s : Sealed) : Nat := sealedLen s.payload.len

/-- The model's bytes of the blob. -/
def render (s : Sealed) : String :=
  s!"sealed/{s.version}/{s.key}/{s.plainHash}/" ++ s.payload.render

end Sealed

/-- A file as a proxy stores and returns it. -/
inductive Blob where
  /-- A payload sent in clear. -/
  | plain (p : Payload)
  /-- A sealed payload, as encrypted. -/
  | sealed (s : Sealed)
  /-- A sealed payload cut to its first `len` bytes. -/
  | cut (s : Sealed) (len : Nat)
  /-- A sealed payload with one byte of a chunk changed. -/
  | tampered (s : Sealed)
  deriving DecidableEq, Repr, Inhabited

namespace Blob

/-- `encrypt_blob(plaintext, sym_key, H(plaintext))`: deterministic in the payload and key. -/
def encrypt (p : Payload) (key : String) (plainHash : String := p.hash) : Blob :=
  .sealed { key, plainHash, payload := p }

/-- What a sender uploads for a recipient: the payload encrypted with their shared key, in clear
for a recipient that does not support encryption. -/
def forRecipient (enc : Encryption) (key : String) (p : Payload) : Blob :=
  if enc == .unsupported then .plain p else encrypt p key

/-- Bytes of the blob (`file_size` of an upload). -/
def len : Blob → Nat
  | .plain p => p.len
  | .sealed s | .tampered s => s.len
  | .cut s n => min n s.len

/-- The model's bytes of the blob. -/
def render : Blob → String
  | .plain p => p.render
  | .sealed s => s.render
  | .cut s n => if n ≥ s.len then s.render else s.render ++ s!"/cut/{n}"
  | .tampered s => s.render ++ "/tampered"

/-- Hex SHA-256 of the bytes on the wire (`blob_hash`). -/
def hash (b : Blob) : String := sha256Hex b.render

/-- The bytes as a payload, for a receiver that does not decrypt them. -/
def raw : Blob → Payload
  | .plain p => p
  | b => .bytes b.render

end Blob

/-- `decrypt_stream` error for an empty blob. -/
def emptyBlobMsg : String := "empty encrypted blob"
/-- `decrypt_stream` error for a piece shorter than a tag. -/
def truncatedBlobMsg : String := "truncated encrypted blob"
/-- `decrypt_stream` error for a chunk that does not open. -/
def authFailedMsg : String := "authentication failed"

/-- `decrypt_stream` error for a blob of another format version. -/
def versionMsg (v : UInt8) : String := s!"unsupported encryption version {v}"

/-- Error of a body none of whose chunks opens: the first piece is too short or fails. -/
def foreignBodyMsg (body : Nat) : String :=
  if body < tagLen then truncatedBlobMsg else authFailedMsg

/-- Error of a sealed body cut short: its chunks open up to the last piece, which is shorter
than a tag, a partial chunk, or a whole chunk no longer flagged final. -/
def cutBodyMsg (body : Nat) : String :=
  let last := if body % encChunkSize == 0 then encChunkSize else body % encChunkSize
  if body == 0 || last < tagLen then truncatedBlobMsg else authFailedMsg

/-- Open a sealed blob kept to its first `len` bytes. -/
private def openSealed (s : Sealed) (len : Nat) (key plainHash : String) :
    Except Error Payload :=
  if len == 0 then .error (.invalidEncryptedBlob emptyBlobMsg)
  else if s.version != encVersion then .error (.invalidEncryptedBlob (versionMsg s.version))
  else
    let authentic := s.key == key && s.plainHash == plainHash
    if len ≥ s.len then
      if authentic then .ok s.payload else .error (.invalidEncryptedBlob (foreignBodyMsg (len - 1)))
    else if authentic then .error (.invalidEncryptedBlob (cutBodyMsg (len - 1)))
    else .error (.invalidEncryptedBlob (foreignBodyMsg (len - 1)))

/-- Error of a file that was never encrypted, read as a blob. -/
def plainBodyMsg (p : Payload) : String :=
  match p.firstByte? with
  | none => emptyBlobMsg
  | some v => if v != encVersion then versionMsg v else foreignBodyMsg (p.len - 1)

/-- `decrypt_blob(blob, sym_key, H(plaintext))`: the payload exactly when the blob is sealed,
whole and unchanged, with this key and plaintext hash. -/
def Blob.decrypt (b : Blob) (key plainHash : String) : Except Error Payload :=
  match b with
  | .plain p => .error (.invalidEncryptedBlob (plainBodyMsg p))
  | .sealed s => openSealed s s.len key plainHash
  | .cut s n => openSealed s (min n s.len) key plainHash
  | .tampered s =>
    if s.version != encVersion then .error (.invalidEncryptedBlob (versionMsg s.version))
    else .error (.invalidEncryptedBlob (foreignBodyMsg (s.len - 1)))

/-- How a receiver reads a downloaded blob (`decrypt_blob_with_shared_key`): as it is with
`unsupported`, decrypted with `required`, decrypted or else as it is with `optional`; the result
must hash to `plainHash`. -/
def Blob.decryptWith (b : Blob) (enc : Encryption) (key plainHash : String) :
    Except Error Payload := do
  let p ← match enc with
    | .unsupported => pure b.raw
    | .required => b.decrypt key plainHash
    | .optional =>
      match b.decrypt key plainHash with
      | .ok p => pure p
      | .error _ => pure b.raw
  if p.hash != plainHash then throw .hashMismatch
  return p

/-! ## Proof of work -/

/-- Leading zero bits of one byte. -/
def byteLeadingZeros (b : UInt8) : Nat := if b == 0 then 8 else 7 - Nat.log2 b.toNat

/-- `leading_zero_bits`: zero bits from the most significant bit of the first byte. -/
def leadingZeroBits : Bytes → Nat
  | [] => 0
  | b :: rest => if b == 0 then 8 + leadingZeroBits rest else byteLeadingZeros b

/-- Whether `nonce` meets `difficulty`: `H(transfer_id ‖ pow_timestamp ‖ nonce)` starts with at
least that many zero bits. -/
def powMeets (transferId powTimestamp nonce : String) (difficulty : Nat) : Bool :=
  leadingZeroBits (sha256 (transferId ++ powTimestamp ++ nonce)) ≥ difficulty

/-- Nonces the search tries: far more than the `2 ^ difficulty` it needs on average. -/
def powSearchBound (difficulty : Nat) : Nat := 2 ^ (difficulty + 8)

/-- The first nonce from `n` meeting `difficulty`, trying `fuel` nonces at most. -/
private def findNonce (transferId powTimestamp : String) (difficulty : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n =>
    if powMeets transferId powTimestamp (toString n) difficulty then some n
    else findNonce transferId powTimestamp difficulty fuel (n + 1)

/-- The least nonce meeting `difficulty`; past `powSearchBound` (never reached in practice) the
bound itself, which the proxy then refuses. -/
def solvePowNonce (transferId powTimestamp : String) (difficulty : Nat) : Nat :=
  (findNonce transferId powTimestamp difficulty (powSearchBound difficulty) 0).getD
    (powSearchBound difficulty)

/-- `solve_pow`: the least nonce meeting `difficulty`, in decimal; `"0"` for difficulty 0. -/
def solvePow (transferId powTimestamp : String) (difficulty : Nat) : String :=
  toString (solvePowNonce transferId powTimestamp difficulty)

end Rgb.Lib.ProxyCrypto
