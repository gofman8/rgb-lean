import Rgb.Consensus.Operation
import Rgb.Consensus.Occurrences

/-!
# Schemas

A schema fixes, for every contract made from it, which global state, owned state
and metadata exist, which operations may carry them and how many, and which
validation routine each operation runs. The schema id commits to all of it, and
genesis commits to the schema id.

Validation routines are AluVM code in RGB. Here a routine is referenced by a
`LibSite` (library id and entry offset), and the model's VM maps each site of a
standard library to a Lean function (see `Rgb.Consensus.Vm`).
-/

namespace Rgb

/-- A routine entry point: library id and offset (`LibSite`). -/
structure LibSite where
  lib : String
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

instance : Encode LibSite := ⟨fun s => encField (encode s.lib ++ encode s.offset)⟩

/-- Fungible state width; only 64-bit unsigned exists. -/
inductive FungibleType where
  | unsigned64Bit
  deriving DecidableEq, Repr, Inhabited

/-- Kind of an owned state type (`OwnedStateSchema`). -/
inductive OwnedStateSchema where
  | declarative
  | fungible (t : FungibleType)
  | structured (sem : SemId)
  deriving DecidableEq, Repr, Inhabited

def OwnedStateSchema.stateType : OwnedStateSchema → StateType
  | .declarative => .void
  | .fungible _ => .fungible
  | .structured _ => .structured

/-- A global state type: its semantic type and how many values the contract may
hold in total (`GlobalStateSchema`, `max_items: u24`). -/
structure GlobalStateSchema where
  semId : SemId
  maxItems : Nat
  deriving DecidableEq, Repr, Inhabited

def GlobalStateSchema.once (s : SemId) : GlobalStateSchema := ⟨s, 1⟩
def GlobalStateSchema.many (s : SemId) : GlobalStateSchema := ⟨s, Bound.u24⟩

structure AssignmentDetails where
  ownedStateSchema : OwnedStateSchema
  name : String
  defaultTransition : TransitionType
  deriving DecidableEq, Repr, Inhabited

structure GlobalDetails where
  globalStateSchema : GlobalStateSchema
  name : String
  deriving DecidableEq, Repr, Inhabited

structure MetaDetails where
  semId : SemId
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- What genesis may carry (`GenesisSchema`). -/
structure GenesisSchema where
  metadata : OrdSet MetaType := {}
  globals : OrdMap GlobalStateType Occurrences := {}
  assignments : OrdMap AssignmentType Occurrences := {}
  validator : Option LibSite := none
  deriving DecidableEq, Repr, Inhabited

/-- What a transition type may carry and spend (`TransitionSchema`). -/
structure TransitionSchema where
  metadata : OrdSet MetaType := {}
  globals : OrdMap GlobalStateType Occurrences := {}
  inputs : OrdMap AssignmentType Occurrences := {}
  assignments : OrdMap AssignmentType Occurrences := {}
  validator : Option LibSite := none
  deriving DecidableEq, Repr, Inhabited

structure TransitionDetails where
  transitionSchema : TransitionSchema
  name : String
  deriving DecidableEq, Repr, Inhabited

/-- `Schema`: every map is a `TinyOrdMap` (at most 255 entries). -/
structure Schema where
  ffv : Ffv := {}
  name : String
  metaTypes : OrdMap MetaType MetaDetails := {}
  globalTypes : OrdMap GlobalStateType GlobalDetails := {}
  ownedTypes : OrdMap AssignmentType AssignmentDetails := {}
  genesis : GenesisSchema
  transitions : OrdMap TransitionType TransitionDetails := {}
  defaultAssignment : Option AssignmentType := none
  deriving DecidableEq, Repr, Inhabited

namespace Schema

/-- The schema id commits to every field. -/
def schemaId (s : Schema) : SchemaId :=
  ⟨Digest.of Tag.schema [encode s.ffv, encode s.name, encode (reprStr s)]⟩

def assignmentType? (s : Schema) (name : String) : Option AssignmentType :=
  (s.ownedTypes.toList.find? (·.2.name == name)).map (·.1)

def globalType? (s : Schema) (name : String) : Option GlobalStateType :=
  (s.globalTypes.toList.find? (·.2.name == name)).map (·.1)

def metaType? (s : Schema) (name : String) : Option MetaType :=
  (s.metaTypes.toList.find? (·.2.name == name)).map (·.1)

def transitionType? (s : Schema) (name : String) : Option TransitionType :=
  (s.transitions.toList.find? (·.2.name == name)).map (·.1)

def defaultTransitionFor? (s : Schema) (t : AssignmentType) : Option TransitionType :=
  (s.ownedTypes.find? t).map (·.defaultTransition)

/-- Every routine the schema references. -/
def libSites (s : Schema) : List LibSite :=
  s.genesis.validator.toList ++ s.transitions.values.filterMap (·.transitionSchema.validator)

/-- Library ids the schema needs. -/
def libs (s : Schema) : List String := (s.libSites.map (·.lib)).eraseDups

end Schema

end Rgb
