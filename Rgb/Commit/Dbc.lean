import Rgb.Commit.Mpc
import Rgb.Bitcoin.Merkle

/-!
# Deterministic Bitcoin commitments, anchors and SPV proofs

The witness transaction carries the MPC commitment in exactly one place: its
first output that is `OP_RETURN` or taproot.
* **Opret**: the output script is `OP_RETURN <32-byte commitment>`.
* **Tapret**: the taproot output key is the internal key tweaked with a script
  tree whose commitment leaf holds the commitment; the proof gives the internal
  key and the partner node of that leaf.

An anchor is the MPC proof of the contract plus the DBC proof. An SPV proof
shows the witness transaction is in a block at a height.
-/

namespace Rgb

/-- Commitment method (`dbc::Method`, `CloseMethod`). -/
inductive DbcMethod where
  | opretFirst
  | tapretFirst
  deriving DecidableEq, Repr, Inhabited

/-- Tapscript of a tap leaf, as far as tapret reads it. -/
inductive TapScript where
  /-- The tapret commitment leaf: 29 `OP_RESERVED`, `OP_RETURN`, 33 pushed bytes. -/
  | tapret (commitment : Digest) (nonce : UInt8)
  | other (s : String)
  deriving DecidableEq, Repr, Inhabited

def TapScript.leafHash : TapScript → Digest
  | .tapret c n => Digest.of Tag.tapLeaf ["tapret", encode c, encode n]
  | .other s => Digest.of Tag.tapLeaf ["script", encode s]

/-- BIP-341 branch: the two child hashes are sorted. -/
def tapBranch (a b : Digest) : Digest :=
  if compare a b != .gt then Digest.of Tag.tapBranch [encode a, encode b]
  else Digest.of Tag.tapBranch [encode b, encode a]

/-- Taproot output key of an internal key and an optional script tree root. -/
def tapTweak (internalKey : String) (root : Option Digest) : Digest :=
  Digest.of Tag.tapTweak [encode internalKey, encode root]

/-- The sibling of the tapret leaf (`TapretNodePartner`). -/
inductive TapretNodePartner where
  | leftNode (h : Digest)
  | rightLeaf (s : TapScript)
  | rightBranch (left right : Digest)
  deriving DecidableEq, Repr, Inhabited

namespace TapretNodePartner

def nodeHash : TapretNodePartner → Digest
  | .leftNode h => h
  | .rightLeaf s => s.leafHash
  | .rightBranch l r => tapBranch l r

/-- The partner is not itself a tapret commitment (`check_no_commitment`). -/
def noCommitment : TapretNodePartner → Bool
  | .rightLeaf (.tapret _ _) => false
  | _ => true

/-- The commitment leaf is placed first in consensus order (`check_ordering`). -/
def ordered (p : TapretNodePartner) (leaf : Digest) : Bool :=
  match p with
  | .leftNode h => compare h leaf != .gt
  | .rightLeaf s => compare leaf s.leafHash != .gt
  | .rightBranch l r => compare leaf (tapBranch l r) != .gt

end TapretNodePartner

/-- Tapret proof: internal key, partner node and nonce (`TapretProof`). -/
structure TapretProof where
  internalKey : String
  partner : Option TapretNodePartner := none
  nonce : UInt8 := 0
  deriving DecidableEq, Repr, Inhabited

/-- The proof per method (`DbcProof`); an opret proof carries no data. -/
inductive DbcProof where
  | tapret (p : TapretProof)
  | opret
  deriving DecidableEq, Repr, Inhabited

def DbcProof.method : DbcProof → DbcMethod
  | .tapret _ => .tapretFirst
  | .opret => .opretFirst

/-- DBC verification failures (`DbcError`). -/
inductive DbcError where
  | noOpretOutput
  | invalidOpretScript
  | commitmentMismatch
  | unrestorableProof
  | proofMismatch
  | impossibleMessage
  | invalidProof
  deriving DecidableEq, Repr

/-- Output key a tapret proof yields for `commitment` (`convolve_commit`). -/
def TapretProof.outputKey (p : TapretProof) (commitment : Digest) : Except DbcError Digest :=
  let leaf := (TapScript.tapret commitment p.nonce).leafHash
  match p.partner with
  | none => .ok (tapTweak p.internalKey (some leaf))
  | some n =>
    if !n.noCommitment then .error .impossibleMessage
    else if !n.ordered leaf then .error .impossibleMessage
    else .ok (tapTweak p.internalKey (some (tapBranch leaf n.nodeHash)))

/-- Verify a DBC proof against the witness transaction (`DbcProof::verify`). -/
def DbcProof.verify (proof : DbcProof) (commitment : Digest) (tx : Tx) : Except DbcError Unit :=
  match proof with
  | .opret =>
    match tx.outputs.find? (·.script.isOpReturn) with
    | none => .error .noOpretOutput
    | some o => match o.script with
      | .opReturn (some c) => if c == commitment then .ok () else .error .commitmentMismatch
      | _ => .error .invalidOpretScript
  | .tapret p =>
    match tx.outputs.find? (·.script.isTaproot) with
    | none => .error .impossibleMessage
    | some o => do
      let q ← p.outputKey commitment
      if o.script == .p2tr q then .ok () else .error .commitmentMismatch

/-- Index of the output that carries the commitment: the first `OP_RETURN` or
taproot output, with its method. -/
def dbcOutput? (tx : Tx) : Option (Nat × DbcMethod) :=
  (tx.outputs.zipIdx.find? fun (o, _) => o.script.isOpReturn || o.script.isTaproot).map
    fun (o, i) => (i, if o.script.isOpReturn then .opretFirst else .tapretFirst)

/-- Anchor of a bundle: MPC proof plus DBC proof (`Anchor<DbcProof>`). -/
structure Anchor where
  mpcProof : Mpc.MerkleProof
  dbcProof : DbcProof
  deriving DecidableEq, Repr, Inhabited

/-! ## Building commitments (wallet side) -/

/-- Put an opret commitment into the first `OP_RETURN` output, adding one at
index 0 when there is none (`set_opret_host` + `set_opret_commitment`). -/
def Tx.withOpretCommitment (tx : Tx) (commitment : Digest) : Tx :=
  match tx.outputs.findIdx? (·.script.isOpReturn) with
  | some i => { tx with outputs := tx.outputs.set i ⟨(tx.outputs[i]?.map (·.value)).getD 0, .opReturn (some commitment)⟩ }
  | none => { tx with outputs := ⟨0, .opReturn (some commitment)⟩ :: tx.outputs }

/-- A tapret output script committing to `commitment` with no other scripts. -/
def tapretScript (internalKey : String) (commitment : Digest) (nonce : UInt8 := 0) : Script :=
  .p2tr (tapTweak internalKey (some (TapScript.tapret commitment nonce).leafHash))

/-! ## SPV proofs -/

/-- Inclusion of a transaction in the block at a height (`SpvProof`): position
and at most 32 sibling hashes. -/
structure SpvProof where
  blockHeight : Nat
  pos : Nat
  merkle : List Digest
  deriving DecidableEq, Repr, Inhabited

/-- Why an SPV proof fails (`SpvValidationError`). -/
inductive SpvValidationError where
  | positionOutOfBounds
  | merkleRootMismatch
  deriving DecidableEq, Repr

/-- Check the proof against the header (`SpvProof::validate`): the position must be
fully consumed by the path, and the computed root must be the header's. -/
def SpvProof.validate (p : SpvProof) (txid : Txid) (header : BlockHeader) :
    Except SpvValidationError Unit :=
  if p.pos >>> p.merkle.length != 0 then .error .positionOutOfBounds
  else if rootFromBranch txid.d p.pos p.merkle != header.merkleRoot then .error .merkleRootMismatch
  else .ok ()

/-- The mined position an SPV proof shows (`verified_pos`); `none` when the block
time is before the first block of the layer 1. -/
def SpvProof.verifiedPos (p : SpvProof) (txid : Txid) (header : BlockHeader) (l : Layer1) :
    Except SpvValidationError (Option WitnessPos) := do
  p.validate txid header
  return if header.time < l.genesisTimestamp then none else some ⟨p.blockHeight, header.time⟩

/-- The SPV proof of a mined transaction of the simulated chain. -/
def Chain.spvProof? (c : Chain) (t : Txid) : Option SpvProof :=
  (c.merkleProof? t).map fun (h, pos, branch) => ⟨h, pos, branch⟩

end Rgb
