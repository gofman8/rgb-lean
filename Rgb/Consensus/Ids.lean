import Rgb.Bitcoin.Tx

/-!
# RGB identifiers and type numbers

Ids are tagged commitments (see `Rgb.Core.Digest`). Schema-level type numbers
are plain 16-bit values chosen by each schema.
-/

namespace Rgb

/-- Contract id: the id of the contract's genesis operation. -/
structure ContractId where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Operation id: tagged hash of the operation commitment (`OpCommitment`). -/
structure OpId where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Schema id: tagged hash of the whole schema. -/
structure SchemaId where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Bundle id: tagged hash of a bundle's input map. -/
structure BundleId where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Concealed seal: tagged hash of a blinded seal (shown as `utxob:...`). -/
structure SecretSeal where
  d : Digest
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : ToString ContractId := ⟨fun c => s!"rgb:{c.d}"⟩
instance : ToString OpId := ⟨fun o => toString o.d⟩
instance : ToString SchemaId := ⟨fun s => s!"rgb:sch:{s.d}"⟩
instance : ToString BundleId := ⟨fun b => toString b.d⟩
instance : ToString SecretSeal := ⟨fun s => s!"utxob:{s.d}"⟩

instance : Encode ContractId := ⟨fun c => encode c.d⟩
instance : Encode OpId := ⟨fun o => encode o.d⟩
instance : Encode SchemaId := ⟨fun s => encode s.d⟩
instance : Encode BundleId := ⟨fun b => encode b.d⟩
instance : Encode SecretSeal := ⟨fun s => encode s.d⟩

/-- Owned state type number. -/
structure AssignmentType where
  v : UInt16
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Global state type number. -/
structure GlobalStateType where
  v : UInt16
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- Metadata type number. -/
structure MetaType where
  v : UInt16
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

/-- State transition type number. -/
structure TransitionType where
  v : UInt16
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode AssignmentType := ⟨fun t => encode t.v⟩
instance : Encode GlobalStateType := ⟨fun t => encode t.v⟩
instance : Encode MetaType := ⟨fun t => encode t.v⟩
instance : Encode TransitionType := ⟨fun t => encode t.v⟩
instance : ToString AssignmentType := ⟨fun t => toString t.v⟩
instance : ToString GlobalStateType := ⟨fun t => toString t.v⟩
instance : ToString MetaType := ⟨fun t => toString t.v⟩
instance : ToString TransitionType := ⟨fun t => toString t.v⟩

/-- The assignment type every standard fungible schema uses for its asset
(`AssignmentType::ASSET`). -/
def AssignmentType.asset : AssignmentType := ⟨4000⟩

/-- Fast-forward version (`RGB/1.<ffv>`); decoding refuses any value but 0. -/
structure Ffv where
  v : UInt16 := 0
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode Ffv := ⟨fun f => encode f.v⟩

/-- The only supported fast-forward version. -/
def Ffv.supported (f : Ffv) : Bool := f.v == 0

/-- An operation output: which assignment of which operation (`Opout`). -/
structure Opout where
  op : OpId
  ty : AssignmentType
  no : UInt16
  deriving DecidableEq, Ord, Hashable, Inhabited, Repr

instance : Encode Opout := ⟨fun o => encField (encode o.op ++ encode o.ty ++ encode o.no)⟩
instance : ToString Opout := ⟨fun o => s!"{o.op}/{o.ty}/{o.no}"⟩

end Rgb
