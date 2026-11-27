import Rgb.Bitcoin.Merkle

/-!
# Witness resolvers

How validation and the stash learn the status of a witness transaction from
layer 1 (`ResolveWitness`). Resolvers apply no confirmation threshold: `mined`
means "in the indexer's best chain"; depth policy belongs to the caller.
-/

namespace Rgb

/-- What a resolver knows about a witness (`WitnessStatus`). -/
inductive WitnessStatus where
  /-- Not found. Counts as archived. -/
  | unresolved
  | resolved (tx : Tx) (ord : WitnessOrd)
  deriving Repr, Inhabited

def WitnessStatus.witnessOrd : WitnessStatus → WitnessOrd
  | .unresolved => .archived
  | .resolved _ o => o

/-- Resolver failures (`WitnessResolverError`). -/
inductive WitnessResolverError where
  | idMismatch (actual expected : Txid)
  | resolverIssue (txid : Option Txid) (msg : String)
  | invalidResolverData
  | wrongChainNet
  | notSupported
  deriving DecidableEq, Repr

/-- A layer-1 resolver (`ResolveWitness` + `ResolveSpvProof`). -/
structure Resolver where
  resolveWitness : Txid → Except WitnessResolverError WitnessStatus
  /-- Header of the best chain at a height; `notSupported` by default. -/
  getBlockHeader : Nat → Except WitnessResolverError BlockHeader := fun _ => .error .notSupported
  checkChainNet : ChainNet → Except WitnessResolverError Unit

/-- A resolver backed by the simulated chain of network `net`. -/
def Chain.resolver (c : Chain) (net : ChainNet) : Resolver where
  resolveWitness t :=
    match c.findMined? t with
    | some (tx, b) => .ok (.resolved tx (.mined ⟨b.height, b.timestamp⟩))
    | none => match c.findMempool? t with
      | some tx => .ok (.resolved tx .tentative)
      | none => .ok .unresolved
  getBlockHeader h := match c.header? h with
    | some hd => .ok hd
    | none => .error (.resolverIssue none "no block at height")
  checkChainNet n := if n == net then .ok () else .error .wrongChainNet

/-- Witnesses carried by a consignment resolve as tentative without asking the
indexer, so an unbroadcast transfer can be validated (`AnyResolver`). -/
def Resolver.withConsignmentTxes (r : Resolver) (txes : List Tx) : Resolver :=
  { r with resolveWitness := fun t =>
      match txes.find? (·.txid == t) with
      | some tx => .ok (.resolved tx .tentative)
      | none => r.resolveWitness t }

/-- A resolver that answers every witness as archived and accepts any chain
(`DumbResolver`, used to validate a genesis-only contract). -/
def Resolver.dumb : Resolver where
  resolveWitness _ := .ok (.resolved default .archived)
  checkChainNet _ := .ok ()

end Rgb
