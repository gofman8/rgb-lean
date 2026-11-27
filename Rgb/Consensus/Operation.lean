import Rgb.Consensus.Seal
import Rgb.Stl.Value

/-!
# Contract operations

A contract is a graph of operations. Genesis creates the contract and its first
state; each state transition spends owned state of earlier operations (its
inputs) and assigns new owned state to seals. Every operation may also add
global state (contract-wide data) and metadata (data for its validation script
only). There are no state extensions.

All state is revealed: amounts and data are always visible to whoever validates
the operation. Only seals can be concealed.
-/

namespace Rgb

/-- Kind of owned state. -/
inductive StateType where
  | void
  | fungible
  | structured
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

/-- Fungible state: a 64-bit unsigned amount (`RevealedValue`, `FungibleState::Bits64`). -/
structure RevealedValue where
  v : UInt64
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

/-- Structured state: strict-encoded data, at most 65535 bytes (`RevealedData`). -/
structure RevealedData where
  v : StrictValue
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Metadata value (`MetaValue`, a `SmallBlob`). -/
abbrev MetaValue := RevealedData

/-- Owned state of any kind (`RevealedState`). -/
inductive RevealedState where
  | void
  | fungible (v : RevealedValue)
  | structured (d : RevealedData)
  deriving DecidableEq, Hashable, Repr, Inhabited

def RevealedState.stateType : RevealedState → StateType
  | .void => .void
  | .fungible _ => .fungible
  | .structured _ => .structured

def RevealedState.amount? : RevealedState → Option UInt64
  | .fungible v => some v.v
  | _ => none

instance : Encode RevealedValue := ⟨fun v => encode v.v⟩
instance : Encode RevealedData := ⟨fun d => encode d.v⟩
instance : Encode RevealedState := ⟨fun
  | .void => "V"
  | .fungible v => "F" ++ encode v
  | .structured d => "D" ++ encode d⟩

/-- The owned state of one assignment type: 1 to 65535 assignments of one kind
(`TypedAssigns`). A declarative assignment carries no data (`VoidState`). -/
inductive TypedAssigns (σ : Type) where
  | declarative (items : List (BuilderSeal σ))
  | fungible (items : List (BuilderSeal σ × RevealedValue))
  | structured (items : List (BuilderSeal σ × RevealedData))
  deriving DecidableEq, Repr, Inhabited

namespace TypedAssigns
variable {σ : Type}

def stateType : TypedAssigns σ → StateType
  | .declarative _ => .void
  | .fungible _ => .fungible
  | .structured _ => .structured

/-- Every assignment as a seal and its state, in order. -/
def items : TypedAssigns σ → List (BuilderSeal σ × RevealedState)
  | .declarative l => l.map (·, .void)
  | .fungible l => l.map fun (s, v) => (s, .fungible v)
  | .structured l => l.map fun (s, d) => (s, .structured d)

def len (a : TypedAssigns σ) : Nat := a.items.length

def seals (a : TypedAssigns σ) : List (BuilderSeal σ) := a.items.map (·.1)

def at? (a : TypedAssigns σ) (no : Nat) : Option (BuilderSeal σ × RevealedState) := a.items[no]?

def mapSeals {τ : Type} (f : BuilderSeal σ → BuilderSeal τ) : TypedAssigns σ → TypedAssigns τ
  | .declarative l => .declarative (l.map f)
  | .fungible l => .fungible (l.map fun (s, v) => (f s, v))
  | .structured l => .structured (l.map fun (s, d) => (f s, d))

def amounts (a : TypedAssigns σ) : List UInt64 := a.items.filterMap (·.2.amount?)

end TypedAssigns

/-- Owned state of an operation by assignment type (`SmallOrdMap`, up to 65535 types). -/
abbrev Assignments (σ : Type) := OrdMap AssignmentType (TypedAssigns σ)

/-- Global state added by an operation: 1 to 65535 values per type, up to 255
types (`GlobalState`, `GlobalValues`). -/
abbrev GlobalState := OrdMap GlobalStateType (List RevealedData)

/-- Metadata of an operation: one value per type, up to 255 types (`Metadata`). -/
abbrev Metadata := OrdMap MetaType MetaValue

/-- Issuer identity: ASCII printable, 1 to 4096 chars; never checked by consensus. -/
structure Identity where
  s : String := "ssi:anonymous"
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

def Identity.valid (i : Identity) : Bool :=
  let cs := i.s.toList
  1 ≤ cs.length && cs.length ≤ 4096 && cs.all Charset.isAsciiPrintable

/-- How seals are closed: the commitment goes into the first `OP_RETURN` or
taproot output of the witness (`SealClosingStrategy`, the only value). -/
inductive SealClosingStrategy where
  | firstOpretOrTapret
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

/-- Compressed public key (33 bytes) of a named secret key. -/
def pubkeyOf (signer : String) : Bytes :=
  0x02 :: Bytes.le (Digest.of "secp256k1:pk" [encode signer]).fingerprint.toNat 32

/-- A 64-byte compact ECDSA signature attached to a transition; not part of its
id. The model keeps the signing key's name and the signed digest. -/
structure Signature where
  signer : String
  msg : Digest
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Sign a digest with a named key. -/
def Signature.sign (signer : String) (msg : Digest) : Signature := ⟨signer, msg⟩

/-- ECDSA verification: the signature is by the key of `pubkey`, over `msg`. -/
def Signature.verify (sig : Signature) (pubkey : Bytes) (msg : Digest) : Bool :=
  pubkeyOf sig.signer == pubkey && sig.msg == msg

structure Genesis where
  ffv : Ffv := {}
  schemaId : SchemaId
  timestamp : Int
  issuer : Identity := {}
  chainNet : ChainNet
  sealClosingStrategy : SealClosingStrategy := .firstOpretOrTapret
  metadata : Metadata := {}
  globals : GlobalState := {}
  assignments : Assignments GenesisSeal := {}
  deriving DecidableEq, Repr, Inhabited

structure Transition where
  ffv : Ffv := {}
  contractId : ContractId
  nonce : UInt64 := 0xFFFFFFFFFFFFFFFF
  transitionType : TransitionType
  metadata : Metadata := {}
  globals : GlobalState := {}
  /-- Spent owned state: 1 to 65535 distinct opouts (`Inputs`). -/
  inputs : List Opout
  assignments : Assignments GraphSeal := {}
  signature : Option Signature := none
  deriving DecidableEq, Repr, Inhabited

/-! ## Operation ids

The id commits to: version, nonce, type (for genesis: schema id, timestamp,
issuer, chain net and closing strategy; for a transition: contract id and
transition type), and the merkle roots of metadata, global state, inputs and
assignments. An assignment commits to its type, its state and its *concealed*
seal, so concealing or revealing a seal never changes the id. The signature is
not committed. -/

/-- Commitment leaf of an assignment: type, state and concealed seal. -/
def assignmentLeaves {σ : Type} [SealKind σ] (a : Assignments σ) : List String :=
  a.toList.flatMap fun (ty, ta) =>
    ta.items.map fun (s, st) => encode ty ++ encode st ++ encode s.toSecret

def globalLeaves (g : GlobalState) : List String :=
  g.toList.flatMap fun (ty, vals) => vals.map fun v => encode ty ++ encode v

def metadataCommit (m : Metadata) : String :=
  encode (m.toList.map fun (k, v) => encode k ++ encode v)

def Genesis.id (g : Genesis) : OpId :=
  ⟨Digest.of Tag.operation
    [encode g.ffv, encode (0xFFFFFFFFFFFFFFFF : UInt64), "G",
      encode g.schemaId, encode g.timestamp, encode g.issuer.s, encode g.chainNet,
      metadataCommit g.metadata, encode (globalLeaves g.globals), encode ([] : List String),
      encode (assignmentLeaves g.assignments)]⟩

def Genesis.contractId (g : Genesis) : ContractId := ⟨g.id.d⟩

def Transition.id (t : Transition) : OpId :=
  ⟨Digest.of Tag.operation
    [encode t.ffv, encode t.nonce, "T", encode t.contractId, encode t.transitionType,
      metadataCommit t.metadata, encode (globalLeaves t.globals), encode t.inputs,
      encode (assignmentLeaves t.assignments)]⟩

/-- Either kind of operation, with seals of transitions (`Operation`). -/
inductive Operation where
  | genesis (g : Genesis)
  | transition (t : Transition)
  deriving DecidableEq, Repr, Inhabited

/-- Operation type as the schema sees it (`OpFullType`). -/
inductive OpFullType where
  | genesis
  | transition (ty : TransitionType)
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

namespace Operation

def id : Operation → OpId
  | genesis g => g.id
  | transition t => t.id

def contractId : Operation → ContractId
  | genesis g => g.contractId
  | transition t => t.contractId

def fullType : Operation → OpFullType
  | genesis _ => .genesis
  | transition t => .transition t.transitionType

/-- Genesis has nonce `u64::MAX`. -/
def nonce : Operation → UInt64
  | genesis _ => 0xFFFFFFFFFFFFFFFF
  | transition t => t.nonce

def metadata : Operation → Metadata
  | genesis g => g.metadata
  | transition t => t.metadata

def globals : Operation → GlobalState
  | genesis g => g.globals
  | transition t => t.globals

def inputs : Operation → List Opout
  | genesis _ => []
  | transition t => t.inputs

/-- Assignments with genesis seals turned into graph seals (`transmutate_seals`). -/
def assignments : Operation → Assignments GraphSeal
  | genesis g => g.assignments.mapValues (TypedAssigns.mapSeals BuilderSeal.toGraph)
  | transition t => t.assignments

/-- The opouts an operation creates. -/
def opouts (op : Operation) : List Opout :=
  op.assignments.toList.flatMap fun (ty, ta) =>
    (List.range ta.len).map fun no => ⟨op.id, ty, no.toUInt16⟩

/-- The state at an opout of this operation, with its seal. -/
def stateAt? (op : Operation) (o : Opout) : Option (BuilderSeal GraphSeal × RevealedState) :=
  if o.op != op.id then none
  else (op.assignments.find? o.ty).bind (·.at? o.no.toNat)

end Operation

end Rgb
