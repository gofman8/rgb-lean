import Rgb.Ops.Psbt

/-!
# Committing bundles to a witness

How a wallet anchors bundles in a transaction (the opret path of
`rgb-psbt-utils`, the only one rgb-lib uses): the bundles of all contracts the
transaction moves go into one MPC tree; its commitment goes into the first
`OP_RETURN` output (one is added at index 0 if there is none); each contract's
anchor is its MPC proof with an opret proof. The result is the fascia the stash
consumes and the witness bundles consignments carry.
-/

namespace Rgb

/-- Commit the transitions of the bundles into `tx` the way rgb-lib colors a
PSBT: push the transitions, flag the opret host, set the entropy and the opret
method, then commit (`rgb_commit`). -/
def commitBundles (tx : Tx) (bundles : List (ContractId × TransitionBundle)) (entropy : UInt64) :
    Except PsbtError Fascia := do
  let p : RgbPsbt := { tx }
  let (p, _) ← p.pushTransitions (bundles.flatMap fun (_, b) => b.knownTransitions.map (·.transition))
  let p := { p.setOpretHost with mpcEntropy := some entropy, closeMethod := some .opretFirst }
  let (_, f) ← p.commit
  return f

/-- The witness bundle of one contract of a fascia. -/
def Fascia.witnessBundle? (f : Fascia) (cid : ContractId) : Option WitnessBundle := do
  let b ← f.bundles.find? cid
  let a ← f.sealWitness.anchor? cid
  return { tx := f.sealWitness.tx, anchor := a, bundle := b }

/-- A transaction spending `inputs` with `outputs` (no commitment yet). -/
def mkTx (inputs : List Outpoint) (outputs : List TxOut) (lockTime : UInt32 := 0) : Tx :=
  { inputs := inputs.map (⟨·, 0xFFFFFFFD⟩), outputs, lockTime }

end Rgb
