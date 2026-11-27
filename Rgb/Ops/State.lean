import Rgb.Consensus.Schema
import Rgb.Bitcoin.Chain

/-!
# Contract state

What a contract's history adds up to (`rgb-ops` `contract`): allocations of
owned state on outputs, and global state ordered by consensus. An allocation
created by a transition counts only while its witness is not archived; a
witness-output seal resolves to an output of that witness.
-/

namespace Rgb

/-- Owned state as stored by the stash (`AllocatedState`; wire tags 0, 1, 2). -/
inductive AllocatedState where
  | void
  | amount (v : UInt64)
  | data (d : RevealedData)
  deriving DecidableEq, Hashable, Repr, Inhabited

def AllocatedState.ofRevealed : RevealedState → AllocatedState
  | .void => .void
  | .fungible v => .amount v.v
  | .structured d => .data d

def AllocatedState.amount? : AllocatedState → Option UInt64
  | .amount v => some v
  | _ => none

/-- A witness and its consensus status (`WitnessInfo`). -/
structure WitnessInfo where
  id : Txid
  ord : WitnessOrd
  deriving DecidableEq, Repr, Inhabited

/-- Owned state on an output (`OutputAssignment`). Two allocations are the same
when their opout and seal are the same. -/
structure OutputAssignment where
  opout : Opout
  outpoint : Outpoint
  state : AllocatedState
  witness : Option Txid
  bundleId : Option BundleId
  deriving DecidableEq, Repr, Inhabited

namespace OutputAssignment

def sameAs (a b : OutputAssignment) : Bool := a.opout == b.opout && a.outpoint == b.outpoint

/-- Visible unless its witness is unknown or archived (`check_witness`). -/
def checkWitness (a : OutputAssignment) (filter : Txid → Option WitnessOrd) : Bool :=
  match a.witness with
  | none => true
  | some w => match filter w with
    | some o => o.isValid
    | none => false

end OutputAssignment

/-- Consensus order of operations for global state (`OpOrd`): genesis first,
then transitions by type, nonce and id. -/
inductive OpOrd where
  | genesis
  | transition (ty : TransitionType) (nonce : UInt64) (opid : OpId)
  deriving DecidableEq, Ord, Repr, Inhabited

/-- Order of a global value: its operation's order, then its index (`GlobalOrd`). -/
structure GlobalOrd where
  opOrd : OpOrd
  idx : UInt16
  deriving DecidableEq, Ord, Repr, Inhabited

/-- A global value with its order. -/
structure GlobalEntry where
  ord : GlobalOrd
  value : RevealedData
  witness : Option Txid
  deriving DecidableEq, Repr, Inhabited

/-- Accumulated state of one contract (`UnfilteredContractState`). -/
structure ContractState where
  contractId : ContractId
  schemaId : SchemaId
  globals : List (GlobalStateType × GlobalEntry) := []
  allocations : List OutputAssignment := []
  deriving Repr, Inhabited

namespace ContractState

/-- Add an operation's global state and its revealed assignments (`add_operation`).
Concealed seals add nothing; an allocation already present is not added twice. -/
def addOperation (st : ContractState) (op : Operation) (witness : Option Txid)
    (bundleId : Option BundleId) : ContractState :=
  let opOrd := match op with
    | .genesis _ => OpOrd.genesis
    | .transition t => OpOrd.transition t.transitionType t.nonce t.id
  let globals := op.globals.toList.flatMap fun (ty, vals) =>
    vals.zipIdx.map fun (v, i) => (ty, GlobalEntry.mk ⟨opOrd, i.toUInt16⟩ v witness)
  let allocs := op.assignments.toList.flatMap fun (ty, ta) =>
    ta.items.zipIdx.filterMap fun ((bs, st), i) =>
      bs.revealed?.map fun s =>
        { opout := ⟨op.id, ty, i.toUInt16⟩
          outpoint := match witness with
            | some w => s.outpointOr w
            | none => s.outpointOr default
          state := AllocatedState.ofRevealed st
          witness := witness
          bundleId := bundleId : OutputAssignment }
  let fresh := allocs.filter fun a => !(st.allocations.any (·.sameAs a))
  { st with globals := st.globals ++ globals, allocations := st.allocations ++ fresh }

/-- Visible allocations: the witness is known and not archived, and the
operation is not invalid. -/
def visible (st : ContractState) (filter : Txid → Option WitnessOrd)
    (invalidOps : List OpId := []) : List OutputAssignment :=
  st.allocations.filter fun a => a.checkWitness filter && !invalidOps.contains a.opout.op

/-- Global values of a type, latest first, at most `limit` (`GlobalStateIter`):
values of archived witnesses are dropped. -/
def globalValues (st : ContractState) (ty : GlobalStateType) (filter : Txid → Option WitnessOrd)
    (limit : Nat) : List RevealedData :=
  let es := (st.globals.filter (·.1 == ty)).map (·.2) |>.filter fun e =>
    match e.witness with
    | none => true
    | some w => (filter w).any WitnessOrd.isValid
  let sorted := es.mergeSort fun a b => compare a.ord b.ord != .gt
  (sorted.reverse.take limit).map (·.value)

end ContractState

/-- Contract information (`ContractInfo`). -/
structure ContractInfo where
  id : ContractId
  schemaId : SchemaId
  issuer : Identity
  issuedAt : Int
  chainNet : ChainNet
  deriving DecidableEq, Repr, Inhabited

def ContractInfo.ofGenesis (g : Genesis) : ContractInfo :=
  ⟨g.contractId, g.schemaId, g.issuer, g.timestamp, g.chainNet⟩

/-- Direction of a history entry (`OpDirection`). -/
inductive OpDirection where
  | issued
  | received
  | sent
  deriving DecidableEq, Repr, Inhabited

/-- Why two contracts do not link (`LinkError`). -/
inductive LinkError where
  | multipleValues
  | noValue
  | valueMismatch
  | invalid
  deriving DecidableEq, Repr

/-- Parent and child link each other exactly when the parent's `link_to` is the
child and the child's `link_from` is the parent (`validate_contracts_link`). -/
def validateContractsLink (parentLinkTo childLinkFrom : Option ContractId)
    (parent child : ContractId) : Except LinkError Unit :=
  match parentLinkTo, childLinkFrom with
  | none, _ => .error .noValue
  | _, none => .error .noValue
  | some to, some fr => if to == child && fr == parent then .ok () else .error .valueMismatch

/-- Why two copies of an operation do not merge (`MergeRevealError`). -/
inductive MergeRevealError where
  | operationMismatch (a b : OpId)
  | signatureMismatch (opid : OpId)
  | txidMismatch (a b : Txid)
  | assignmentsDifferentKeys
  | contractMismatch
  deriving DecidableEq, Repr

/-- Merge two copies of the same transition: a revealed seal wins over a
concealed one; signatures must agree (`MergeReveal for Transition`). -/
def Transition.mergeReveal (a b : Transition) : Except MergeRevealError Transition := do
  if a.id != b.id then throw (.operationMismatch a.id b.id)
  for (ty, _) in b.assignments.toList do
    if !a.assignments.contains ty then throw .assignmentsDifferentKeys
  let merged := a.assignments.toList.map fun (ty, ta) =>
    match b.assignments.find? ty with
    | none => (ty, ta)
    | some tb =>
      let pick (x y : BuilderSeal GraphSeal) : BuilderSeal GraphSeal :=
        if y.isRevealed then y else x
      let sealsB := tb.seals
      (ty,
        match ta with
        | .declarative l => .declarative (l.zipIdx.map fun (s, i) => (sealsB[i]?.map (pick s)).getD s)
        | .fungible l => .fungible (l.zipIdx.map fun ((s, v), i) => ((sealsB[i]?.map (pick s)).getD s, v))
        | .structured l => .structured (l.zipIdx.map fun ((s, d), i) => ((sealsB[i]?.map (pick s)).getD s, d)))
  let sig ← match a.signature, b.signature with
    | none, none => pure none
    | some s, none | none, some s => pure (some s)
    | some s, some s' => if s == s' then pure (some s) else throw (.signatureMismatch a.id)
  return { a with assignments := ⟨merged⟩, signature := sig }

end Rgb
