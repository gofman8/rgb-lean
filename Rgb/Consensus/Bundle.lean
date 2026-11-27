import Rgb.Consensus.Operation

/-!
# Transition bundles

All transitions of one contract that a witness transaction closes seals for go
into one bundle. The bundle maps every spent opout to the transition that spends
it; its id commits to that map only, so a party can receive the bundle with only
the transitions it needs (the others stay unknown) and still check the
commitment. Transitions of a bundle may spend each other's outputs.
-/

namespace Rgb

/-- A transition revealed inside a bundle, with its id. -/
structure KnownTransition where
  opid : OpId
  transition : Transition
  deriving DecidableEq, Repr, Inhabited

/-- `TransitionBundle`: input map of 1 to 65535 entries and 1 to 65535 known transitions. -/
structure TransitionBundle where
  inputMap : OrdMap Opout OpId
  knownTransitions : List KnownTransition
  deriving DecidableEq, Repr, Inhabited

/-- Ways a transition does not fit a bundle. -/
inductive BundleError where
  /-- The transition is not referenced by the input map (`UnrelatedTransition`). -/
  | unrelatedTransition (opid : OpId)
  /-- A known transition is not referenced by the input map (`UnrelatedTransitions`). -/
  | unrelatedTransitions
  deriving DecidableEq, Repr

namespace TransitionBundle

/-- The bundle id commits to the input map only. -/
def bundleId (b : TransitionBundle) : BundleId :=
  ⟨Digest.of Tag.bundle [encode b.inputMap]⟩

def inputMapOpids (b : TransitionBundle) : OrdSet OpId := OrdSet.ofList b.inputMap.values

def knownOpids (b : TransitionBundle) : OrdSet OpId :=
  OrdSet.ofList (b.knownTransitions.map (·.opid))

/-- Every known transition is referenced by the input map (`check_opid_commitments`). -/
def checkOpidCommitments (b : TransitionBundle) : Except BundleError Unit :=
  if b.knownOpids.isSubset b.inputMapOpids then .ok () else .error .unrelatedTransitions

def knows (b : TransitionBundle) (opid : OpId) : Bool := b.knownTransitions.any (·.opid == opid)

def transition? (b : TransitionBundle) (opid : OpId) : Option Transition :=
  (b.knownTransitions.find? (·.opid == opid)).map (·.transition)

/-- Sort known transitions so each follows the bundle transitions it spends from,
keeping their order otherwise (`sort_known_transitions`). -/
def sortKnown (b : TransitionBundle) : TransitionBundle :=
  let rec place (fuel : Nat) (pending : List KnownTransition) (out : List KnownTransition) :
      List KnownTransition :=
    match fuel with
    | 0 => out ++ pending
    | fuel + 1 =>
      match pending.find? (fun kt => kt.transition.inputs.all fun i =>
          !(pending.any fun p => p.opid == i.op && p.opid != kt.opid)) with
      | none => out ++ pending
      | some kt => place fuel (pending.filter (·.opid != kt.opid)) (out ++ [kt])
  { b with knownTransitions := place b.knownTransitions.length b.knownTransitions [] }

/-- Reveal a transition the input map references (`reveal_transition`): returns
whether it was added. -/
def revealTransition (b : TransitionBundle) (t : Transition) :
    Except BundleError (TransitionBundle × Bool) :=
  let opid := t.id
  if !(b.inputMapOpids.contains opid) then .error (.unrelatedTransition opid)
  else if b.knows opid then .ok (b, false)
  else .ok (({ b with knownTransitions := b.knownTransitions ++ [KnownTransition.mk opid t] } : TransitionBundle).sortKnown, true)

/-- Keep only the transition `opid`, concealing the others (`to_concealed_except`). -/
def concealedExcept (b : TransitionBundle) (opid : OpId) : Except BundleError TransitionBundle :=
  match b.knownTransitions.filter (·.opid == opid) with
  | [] => .error (.unrelatedTransition opid)
  | kts => .ok { b with knownTransitions := kts }

/-- Reveal a seal wherever its concealed form appears (`reveal_seal`). -/
def revealSeal (b : TransitionBundle) (s : GraphSeal) : TransitionBundle :=
  { b with knownTransitions := b.knownTransitions.map fun kt =>
      { kt with transition := { kt.transition with
          assignments := kt.transition.assignments.mapValues
            (TypedAssigns.mapSeals (·.reveal s)) } } }

/-- Build a bundle from transitions: each input of each transition maps to it. -/
def ofTransitions (ts : List Transition) : TransitionBundle :=
  { inputMap := OrdMap.ofList (ts.flatMap fun t => t.inputs.map (·, t.id))
    knownTransitions := ts.map fun t => ⟨t.id, t⟩ }

end TransitionBundle

end Rgb
