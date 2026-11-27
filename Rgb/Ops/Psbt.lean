import Rgb.Ops.Consignment

/-!
# RGB data in a PSBT (`rgb-psbt-utils`)

A wallet colors a PSBT by storing in it the transitions it creates, for each
contract a map from every spent opout to the transition spending it, the
commitment method, and on the host output the MPC messages and entropy.
Committing (`rgb_commit`) groups the transitions into one bundle per contract,
puts one MPC message per contract on the host output, builds the MPC tree,
writes its commitment into the first `OP_RETURN` output, and returns the fascia.

Pushing a transition that spends an opout another transition already spends is
a double spend and is refused; pushing transitions is all or nothing.
-/

namespace Rgb

/-- Errors of RGB PSBT operations (`RgbPsbtError`, `DbcPsbtError`, `MpcPsbtError`). -/
inductive PsbtError where
  | doubleSpend
  | unrelatedTransitions (stored pushed : OpId)
  | noContracts
  | noContractConsumers
  | invalidTransitionsNumber (c : ContractId) (n : Nat)
  | invalidInputsNumber (n : Nat)
  | noCloseMethod
  | noHostOutput (m : DbcMethod)
  | noProperOutput (m : DbcMethod)
  | txOutputsModifiable
  | opretProhibited
  | outputAlreadyHasCommitment
  | finalized
  | mpc (e : Mpc.MpcError)
  deriving DecidableEq, Repr

/-- A PSBT with its RGB data. -/
structure RgbPsbt where
  tx : Tx
  /-- Transitions by id (`RGB/0x01`). -/
  transitions : List (OpId × Transition) := []
  /-- Per contract, the spent opouts and the transition spending each (`RGB/0x04`). -/
  consumers : List (ContractId × OrdMap Opout OpId) := []
  /-- Commitment method (`RGB/0x02`). -/
  closeMethod : Option DbcMethod := none
  /-- Output flagged as the opret host. -/
  opretHost : Option Nat := none
  mpcEntropy : Option UInt64 := none
  /-- Outputs may still change (PSBT global `tx_modifiable`). -/
  modifiable : Bool := false
  /-- The MPC commitment was written. -/
  committed : Bool := false
  deriving Repr, Inhabited

namespace RgbPsbt

def consumersOf (p : RgbPsbt) (c : ContractId) : OrdMap Opout OpId :=
  ((p.consumers.find? (·.1 == c)).map (·.2)).getD {}

/-- Add transitions (`push_rgb_transitions`): a transition already present must be
the same one; every spent opout gets its spender, and an opout spent by another
transition is a double spend. Returns the number of new transitions. -/
def pushTransitions (p : RgbPsbt) (ts : List Transition) : Except PsbtError (RgbPsbt × Nat) := do
  let mut q := p
  let mut added := 0
  for t in ts do
    let opid := t.id
    match q.transitions.find? (·.1 == opid) with
    | some (_, stored) => if stored.id != opid then throw (.unrelatedTransitions stored.id opid)
    | none =>
      q := { q with transitions := q.transitions ++ [(opid, t)] }
      added := added + 1
    let mut cons := q.consumersOf t.contractId
    for i in t.inputs do
      match cons.find? i with
      | some other => if other != opid then throw .doubleSpend
      | none => cons := cons.insert i opid
    q := { q with consumers := (q.consumers.filter (·.1 != t.contractId)) ++ [(t.contractId, cons)] }
  return (q, added)

/-- Flag the first `OP_RETURN` output as opret host, adding one at index 0 when
there is none (`set_opret_host`). -/
def setOpretHost (p : RgbPsbt) : RgbPsbt :=
  match p.tx.outputs.findIdx? (·.script.isOpReturn) with
  | some i => { p with opretHost := some i }
  | none => { p with tx := { p.tx with outputs := ⟨0, .opReturn none⟩ :: p.tx.outputs }, opretHost := some 0
                     transitions := p.transitions }

/-- One bundle per contract: its consumer map as input map, its known transitions
parents first (`rgb_bundles`). -/
def bundles (p : RgbPsbt) : Except PsbtError (List (ContractId × TransitionBundle)) := do
  let mut out : List (ContractId × TransitionBundle) := []
  for (c, cons) in p.consumers do
    if cons.isEmpty then throw .noContractConsumers
    if cons.size > Bound.u16 then throw (.invalidInputsNumber cons.size)
    let opids := cons.values.eraseDups
    let known := (opids.filterMap fun o => (p.transitions.find? (·.1 == o)).map fun (_, t) => KnownTransition.mk o t)
    if known.isEmpty || known.length > Bound.u16 then throw (.invalidTransitionsNumber c known.length)
    out := out ++ [(c, ({ inputMap := cons, knownTransitions := known } : TransitionBundle).sortKnown)]
  if out.isEmpty then throw .noContracts
  return out

/-- Commit (`rgb_commit` with opret): needs a close method, a host and unmodifiable
outputs; writes the MPC commitment into the first `OP_RETURN` output. -/
def commit (p : RgbPsbt) : Except PsbtError (RgbPsbt × Fascia) := do
  if p.committed then throw .finalized
  let bs ← p.bundles
  let some m := p.closeMethod | throw .noCloseMethod
  if m != .opretFirst then throw (.noProperOutput m)
  let some _ := p.opretHost | throw (.noHostOutput m)
  if p.modifiable then throw .txOutputsModifiable
  let msgs := OrdMap.ofList (bs.map fun (c, b) => (c, b.bundleId))
  let tree ← (Mpc.MerkleTree.tryCommit msgs (p.mpcEntropy.getD 0)).mapError .mpc
  let tx := p.tx.withOpretCommitment tree.commitment
  return ({ p with tx, committed := true }, ⟨⟨tx, tree, .opret, none, []⟩, OrdMap.ofList bs⟩)

end RgbPsbt

end Rgb
