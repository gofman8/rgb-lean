import Rgb.Ops.Consignment

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

/-- Why commitment fails (`CommitError` subset used by rgb-lib). -/
inductive CommitError where
  | noContracts
  | mpc (e : Mpc.MpcError)
  | invalidInputsNumber (n : Nat)
  deriving DecidableEq, Repr

/-- Commit the bundles into `tx` (`rgb_commit` with `OpretFirst`). -/
def commitBundles (tx : Tx) (bundles : List (ContractId × TransitionBundle)) (entropy : UInt64) :
    Except CommitError Fascia := do
  if bundles.isEmpty then throw .noContracts
  for (_, b) in bundles do
    if b.inputMap.size > Bound.u16 then throw (.invalidInputsNumber b.inputMap.size)
  let msgs := OrdMap.ofList (bundles.map fun (c, b) => (c, b.bundleId))
  let tree ← (Mpc.MerkleTree.tryCommit msgs entropy).mapError .mpc
  let tx' := tx.withOpretCommitment tree.commitment
  return ⟨⟨tx', tree, .opret, none, []⟩, OrdMap.ofList bundles⟩

/-- The witness bundle of one contract of a fascia. -/
def Fascia.witnessBundle? (f : Fascia) (cid : ContractId) : Option WitnessBundle := do
  let b ← f.bundles.find? cid
  let a ← f.sealWitness.anchor? cid
  return { tx := f.sealWitness.tx, anchor := a, bundle := b }

/-- A transaction spending `inputs` with `outputs` (no commitment yet). -/
def mkTx (inputs : List Outpoint) (outputs : List TxOut) (lockTime : UInt32 := 0) : Tx :=
  { inputs := inputs.map (⟨·, 0xFFFFFFFD⟩), outputs, lockTime }

end Rgb
