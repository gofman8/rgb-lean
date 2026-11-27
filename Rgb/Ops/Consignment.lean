import Rgb.Consensus.Validation

/-!
# Consignments

What one party sends another (`rgb-ops` containers). A consignment holds the
contract genesis and, for a transfer, the witness bundles of every operation in
the history of the transferred state: each bundle with its full witness
transaction, an optional SPV proof and its anchor. It carries no schema, types
or scripts: the receiver validates against the schema rules it imported.

* A **contract** consignment is genesis only (an issuance or an imported contract).
* A **transfer** consignment adds bundles. It is not addressed: the receiver
  finds its state by its concealed seals or outpoints (`assignmentsTo`).
-/

namespace Rgb

/-- Tag of consignment ids. -/
def consignmentTag : String := "urn:lnp-bp:rgb:consignment#2024-03-11"

/-- A bundle with its witness (`WitnessBundle`); equality of witness bundles is
by witness txid. -/
structure WitnessBundle where
  tx : Tx
  spvProof : Option SpvProof := none
  anchor : Anchor
  bundle : TransitionBundle
  deriving DecidableEq, Repr, Inhabited

def WitnessBundle.witnessId (w : WitnessBundle) : Txid := w.tx.txid

/-- Consignment format version (`ConsignmentVer`): only V1 decodes. -/
inductive ConsignmentVer where
  | v1
  deriving DecidableEq, Repr, Inhabited

structure Consignment where
  version : ConsignmentVer := .v1
  /-- `true`: transfer consignment; `false`: contract consignment. -/
  transfer : Bool
  genesis : Genesis
  bundles : List WitnessBundle := []
  deriving DecidableEq, Repr, Inhabited

namespace Consignment

def contractId (c : Consignment) : ContractId := c.genesis.contractId
def schemaId (c : Consignment) : SchemaId := c.genesis.schemaId

/-- Consignment id: version, type, contract, genesis and every witness bundle. -/
def consignmentId (c : Consignment) : Digest :=
  Digest.of consignmentTag [encode c.transfer, encode c.contractId, reprStr c.genesis,
    encode (c.bundles.map fun b => reprStr b)]

def toConsensusInput (c : Consignment) : ConsensusInput :=
  ⟨c.genesis, c.bundles.map fun w => (w.bundle, w.anchor, w.tx, w.spvProof)⟩

/-- Opouts spent by any bundle's input map (`spent_opouts`). -/
def spentOpouts (c : Consignment) : List Opout := c.bundles.flatMap (·.bundle.inputMap.keys)

/-- Known transitions none of whose outputs is spent in the consignment
(`terminal_ops`). -/
def terminalOps (c : Consignment) : List OpId :=
  let spent := c.spentOpouts
  (c.bundles.flatMap (·.bundle.knownTransitions)).filterMap fun kt =>
    let outs := (Operation.transition kt.transition).opouts
    if outs.any spent.contains then none else some kt.opid

/-- An assignment matching what a receiver looks for (`AssignmentMatch`). -/
structure AssignmentMatch where
  witnessId : Option Txid
  opout : Opout
  builderSeal : BuilderSeal GraphSeal
  deriving DecidableEq, Repr, Inhabited

/-- Assignments to given concealed seals or outpoints (`assignments_to`): a seal
matches by its concealed form (revealed or not) or, when revealed, by its
outpoint (a witness-output seal resolves to the witness of its bundle). -/
def assignmentsTo (c : Consignment) (secrets : List SecretSeal) (outpoints : List Outpoint) :
    List AssignmentMatch :=
  let matchOp (op : Operation) (w : Option Txid) : List AssignmentMatch :=
    op.assignments.toList.flatMap fun (ty, ta) =>
      ta.items.zipIdx.filterMap fun ((bs, _), no) =>
        let bySecret := secrets.contains bs.toSecret
        let byOutpoint := match bs.revealed? with
          | some s => match w with
            | some wid => outpoints.contains (s.outpointOr wid)
            | none => (s.outpoint?.map outpoints.contains).getD false
          | none => false
        if bySecret || byOutpoint then some ⟨w, ⟨op.id, ty, no.toUInt16⟩, bs⟩ else none
  -- genesis seals match as genesis seals, then become graph seals
  let genesisMatches := c.genesis.assignments.toList.flatMap fun (ty, ta) =>
    ta.items.zipIdx.filterMap fun ((bs, _), no) =>
      let bySecret := secrets.contains bs.toSecret
      let byOutpoint := (bs.revealed?.map fun s => outpoints.contains s.outpoint).getD false
      if bySecret || byOutpoint then some ⟨none, ⟨c.genesis.id, ty, no.toUInt16⟩, bs.toGraph⟩ else none
  genesisMatches ++ c.bundles.flatMap fun w =>
    w.bundle.knownTransitions.flatMap fun kt => matchOp (.transition kt.transition) (some w.witnessId)

/-- Reveal concealed seals the receiver knows (`reveal_known_seals`). -/
def revealSeals (c : Consignment) (known : List GraphSeal) : Consignment :=
  { c with bundles := c.bundles.map fun w =>
      { w with bundle := known.foldl TransitionBundle.revealSeal w.bundle } }

/-- The contract part of a consignment (`into_contract`). -/
def intoContract (c : Consignment) : Consignment := { c with transfer := false, bundles := [] }

end Consignment

/-! ## Validation of consignments -/

/-- Phase 1 with the container checks (`validate_deterministic`): a consignment
of the wrong type, or a contract consignment with bundles, is refused. -/
def Consignment.validateDeterministic (c : Consignment) (expectTransfer : Bool) (rules : SchemaRules)
    (cfg : ValidationConfig) : Except ValidationError PendingValidation := do
  if c.transfer != expectTransfer then throw (.invalidConsignment (.custom "invalid consignment type"))
  if !c.transfer && !c.bundles.isEmpty then
    throw (.invalidConsignment (.custom "contract consignment must not contain bundles"))
  Rgb.validateDeterministic rules c.toConsensusInput cfg

/-- A validated consignment and its status (`ValidConsignment`). -/
structure ValidConsignment where
  consignment : Consignment
  status : Status
  deriving DecidableEq, Repr, Inhabited

/-- Full validation (`Consignment::validate`): phase 1, then every witness
resolved, then refused if a routine pushed a claim (claims need the two-phase API). -/
def Consignment.validate (c : Consignment) (expectTransfer : Bool) (rules : SchemaRules) (r : Resolver)
    (cfg : ValidationConfig) : Except ValidationError ValidConsignment := do
  let pv ← c.validateDeterministic expectTransfer rules cfg
  let pv ← pv.resolveAll r
  if !pv.pendingClaims.isEmpty then throw (.pendingClaims pv.pendingClaims.length)
  return ⟨c, pv.finalize⟩

/-- Validation that also confirms claims with a claim checker (the two-phase API
with `resolve_all_claims`): an unconfirmed claim is refused with its operation. -/
def Consignment.validateWithClaims (c : Consignment) (expectTransfer : Bool) (rules : SchemaRules)
    (r : Resolver) (cfg : ValidationConfig) (confirmed : Claim → Bool) :
    Except (ValidationError ⊕ OpId) ValidConsignment := do
  let pv ← (c.validateDeterministic expectTransfer rules cfg).mapError Sum.inl
  let pv ← (pv.resolveAll r).mapError Sum.inl
  let mut pv := pv
  for cl in pv.pendingClaims do
    if !confirmed cl then throw (Sum.inr cl.opid)
    pv ← (pv.resolveClaim cl).mapError Sum.inl
  return ⟨c, pv.finalize⟩

/-! ## Fascia and seal witnesses -/

/-- A witness as the stash keeps it (`SealWitness`): the transaction, the whole
MPC tree it commits to, the DBC proof and an optional SPV proof. -/
structure SealWitness where
  tx : Tx
  mpcTree : Mpc.MerkleTree
  dbcProof : DbcProof
  spvProof : Option SpvProof := none
  deriving DecidableEq, Repr, Inhabited

/-- What a completed PSBT exports for the stash (`Fascia`): the seal witness and
one bundle per contract. -/
structure Fascia where
  sealWitness : SealWitness
  bundles : OrdMap ContractId TransitionBundle
  deriving DecidableEq, Repr, Inhabited

def Fascia.witnessId (f : Fascia) : Txid := f.sealWitness.tx.txid

/-- Anchor of one contract's bundle in a seal witness (`to_merkle_proof`). -/
def SealWitness.anchor? (w : SealWitness) (cid : ContractId) : Option Anchor :=
  (w.mpcTree.proof? cid).map fun p => ⟨p, w.dbcProof⟩

end Rgb
