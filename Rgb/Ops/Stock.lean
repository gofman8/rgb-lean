import Rgb.Ops.Witness
import Rgb.Ops.State

/-!
# The stash (`Stock`)

Everything a wallet knows about its contracts: imported schemas, geneses,
bundles, witnesses with their status, revealed secret seals, and indexes from
outputs and secret seals to opouts. State is never marked spent here: whether an
allocation is spent is decided by the wallet's own UTXO set.

State is *visible* when the bundle that created it has a stored witness that is
not archived and, for owned state, its operation is not marked invalid. A
witness-output seal lands on the same output index of every witness of its
bundle. When a witness becomes archived (reorg, replacement) the operations of
bundles left without a valid witness, and everything built on them, become
invalid; they become valid again when a witness is valid again.
-/

namespace Rgb

/-- Owned state as stored: the seal as defined (no txid: an output of the witness). -/
structure AllocRow where
  contractId : ContractId
  opout : Opout
  sealTxid : Option Txid
  vout : UInt32
  bundleId : Option BundleId
  state : AllocatedState
  deriving DecidableEq, Repr, Inhabited

/-- Global state as stored. -/
structure GlobalRow where
  contractId : ContractId
  ty : GlobalStateType
  ord : GlobalOrd
  value : RevealedData
  bundleId : Option BundleId
  deriving DecidableEq, Repr, Inhabited

/-- Missing or contradictory references (`Inconsistency`). -/
inductive Inconsistency where
  | contractAbsent (c : ContractId)
  | schemaAbsent (s : SchemaId)
  | witnessAbsent (t : Txid)
  | witnessMissesContract (t : Txid) (b : BundleId) (c : ContractId)
  | bundleAbsent (b : BundleId)
  | opBundleAbsent (o : OpId)
  | outpointUnknown (o : Outpoint) (c : ContractId)
  | distinctBundleContract (b : BundleId)
  | bundleWitnessUnknown (b : BundleId)
  deriving DecidableEq, Repr

/-- Stash errors (`StockError`, with the input errors of composition and fascia). -/
inductive StockError where
  | schemaNotImported (s : SchemaId)
  | inconsistency (i : Inconsistency)
  /-- The best witness of a needed bundle is archived; a consignment whose bundle
  has no valid witness is stale. -/
  | absentValidWitness
  | witnessUnresolved (t : Txid) (e : WitnessResolverError)
  | bundlesInconsistency
  /-- A requested transition is concealed in its stored bundle (`ConsignError::Concealed`). -/
  | concealed (b : BundleId) (o : OpId)
  | unrelatedTransition (o : OpId)
  /-- A fascia has no bundle for the contract (`ConsignError::UnrelatedContract`). -/
  | unrelatedContract (c : ContractId)
  | noRequestedTransition (b : BundleId)
  /-- A fascia bundle knows a transition its input map does not reference. -/
  | invalidBundle (c : ContractId) (b : BundleId)
  | mergeReveal (e : MergeRevealError)
  deriving DecidableEq, Repr

structure Stock where
  schemas : List SchemaRules := []
  geneses : List Genesis := []
  bundles : List (BundleId × TransitionBundle) := []
  witnesses : List SealWitness := []
  ords : List (Txid × WitnessOrd) := []
  secretSeals : List (SecretSeal × GraphSeal) := []
  invalidOps : List OpId := []
  opBundle : List (OpId × BundleId) := []
  bundleContract : List (BundleId × ContractId) := []
  bundleWitnesses : List (BundleId × Txid) := []
  /-- Spend edges: spent opout, spending operation, its bundle. -/
  opInputs : List (Opout × OpId × BundleId) := []
  outpointOpouts : List (ContractId × Outpoint × Opout) := []
  secretOpouts : List (ContractId × SecretSeal × Opout) := []
  allocs : List AllocRow := []
  globals : List GlobalRow := []
  deriving Repr, Inhabited

namespace Stock

/-! ## Lookups -/

def rules? (s : Stock) (id : SchemaId) : Option SchemaRules := s.schemas.find? (·.schema.schemaId == id)
def genesis? (s : Stock) (cid : ContractId) : Option Genesis := s.geneses.find? (·.contractId == cid)
def bundle? (s : Stock) (b : BundleId) : Option TransitionBundle := (s.bundles.find? (·.1 == b)).map (·.2)
def witness? (s : Stock) (t : Txid) : Option SealWitness := s.witnesses.find? (·.tx.txid == t)
def ord? (s : Stock) (t : Txid) : Option WitnessOrd := (s.ords.find? (·.1 == t)).map (·.2)
def bundleOf? (s : Stock) (o : OpId) : Option BundleId := (s.opBundle.find? (·.1 == o)).map (·.2)
def witnessIdsOf (s : Stock) (b : BundleId) : List Txid :=
  (s.bundleWitnesses.filter (·.1 == b)).map (·.2) |>.eraseDups
def bundlesOfWitness (s : Stock) (t : Txid) : List BundleId :=
  (s.bundleWitnesses.filter (·.2 == t)).map (·.1) |>.eraseDups
def opsInBundle (s : Stock) (b : BundleId) : List OpId := (s.opBundle.filter (·.2 == b)).map (·.1)
def childOps (s : Stock) (o : OpId) : List OpId :=
  ((s.opInputs.filter fun (i, _, _) => i.op == o).map (·.2.1)).eraseDups

/-- The bundle has a stored witness that is not archived. -/
def bundleHasValidWitness (s : Stock) (b : BundleId) : Bool :=
  (s.witnessIdsOf b).any fun t => (s.ord? t).any WitnessOrd.isValid

/-- Best witness of a set (`select_valid_witness`): every id needs a stored
status; the least status wins (ties: smallest txid); archived is refused. -/
def selectValidWitness (s : Stock) (ids : List Txid) : Except StockError (Txid × WitnessOrd) := do
  let mut best : Option (Txid × WitnessOrd) := none
  for t in ids.mergeSort (fun a b => compare a b != .gt) do
    match s.ord? t with
    | none => throw (.inconsistency (.witnessAbsent t))
    | some o => match best with
      | none => best := some (t, o)
      | some (_, bo) => if compare o bo == .lt then best := some (t, o)
  match best with
  | none => throw (.inconsistency (.witnessAbsent default))
  | some (t, o) => if o.isValid then return (t, o) else throw .absentValidWitness

/-! ## Storing -/

/-- Import a schema with its scripts (`import_schema_definition`); importing twice changes nothing. -/
def importSchema (s : Stock) (r : SchemaRules) : Stock :=
  if (s.rules? r.schema.schemaId).isSome then s else { s with schemas := s.schemas ++ [r] }

/-- Remember a seal the wallet will receive on, so its concealed form can be revealed. -/
def storeSecretSeal (s : Stock) (g : GraphSeal) : Stock :=
  if s.secretSeals.any (·.1 == g.conceal) then s
  else { s with secretSeals := s.secretSeals ++ [(g.conceal, g)] }

private def putWitnessOrd (s : Stock) (t : Txid) (o : WitnessOrd) : Stock :=
  { s with ords := (s.ords.filter (·.1 != t)) ++ [(t, o)] }

/-- Index and store an operation's assignments: revealed seals give rows and
outpoint entries (a witness-output seal under `witness`), concealed ones give
secret-seal entries. -/
private def addAssignments (s : Stock) (cid : ContractId) (op : Operation) (witness : Option Txid)
    (bundle : Option BundleId) : Stock :=
  op.assignments.toList.foldl (fun s (ty, ta) =>
    ta.items.zipIdx.foldl (fun s ((bs, st), no) =>
      let opout : Opout := ⟨op.id, ty, no.toUInt16⟩
      match bs.revealed? with
      | some g =>
        let row : AllocRow := ⟨cid, opout, g.outpoint?.map (·.txid), g.vout, bundle, .ofRevealed st⟩
        let idx := match g.outpoint?, witness with
          | some o, _ => some o
          | none, some w => some ⟨w, g.vout⟩
          | none, none => none
        { s with allocs := if s.allocs.contains row then s.allocs else s.allocs ++ [row]
                 outpointOpouts := match idx with
                   | some o => if s.outpointOpouts.contains (cid, o, opout) then s.outpointOpouts
                     else s.outpointOpouts ++ [(cid, o, opout)]
                   | none => s.outpointOpouts }
      | none =>
        { s with secretOpouts := s.secretOpouts ++ [(cid, bs.toSecret, opout)] }) s) s

private def addGlobals (s : Stock) (cid : ContractId) (op : Operation) (bundle : Option BundleId) : Stock :=
  let rows := (op.globalEntries none).map fun (ty, e) => GlobalRow.mk cid ty e.ord e.value bundle
  { s with globals := s.globals ++ rows.filter (fun r => !s.globals.contains r) }

/-- Store genesis, merging revealed seals into a stored copy. -/
def consumeGenesis (s : Stock) (g : Genesis) : Stock :=
  let cid := g.contractId
  let s := if (s.genesis? cid).isSome then s else { s with geneses := s.geneses ++ [g] }
  let s := addGlobals s cid (.genesis g) none
  addAssignments s cid (.genesis g) none none

/-- Index a bundle under a witness (`index_bundle`) and store its known transitions. -/
def consumeBundle (s : Stock) (cid : ContractId) (b : TransitionBundle) (witness : Txid) :
    Except StockError Stock := do
  let bid := b.bundleId
  if let some c := (s.bundleContract.find? (·.1 == bid)).map (·.2) then
    if c != cid then throw (.inconsistency (.distinctBundleContract bid))
  let mut s := { s with
    bundleContract := if s.bundleContract.any (·.1 == bid) then s.bundleContract else s.bundleContract ++ [(bid, cid)]
    bundleWitnesses := if s.bundleWitnesses.contains (bid, witness) then s.bundleWitnesses
      else s.bundleWitnesses ++ [(bid, witness)] }
  -- merge the bundle with a stored copy: transitions known in either stay known
  let merged := match s.bundle? bid with
    | none => b
    | some old => b.knownTransitions.foldl (fun (acc : TransitionBundle) (kt : KnownTransition) =>
        if acc.knows kt.opid then acc else { acc with knownTransitions := acc.knownTransitions ++ [kt] }) old
  s := { s with bundles := (s.bundles.filter (·.1 != bid)) ++ [(bid, merged.sortKnown)] }
  for kt in b.knownTransitions do
    let t := kt.transition
    s := { s with
      opBundle := if s.opBundle.any (·.1 == kt.opid) then s.opBundle else s.opBundle ++ [(kt.opid, bid)]
      opInputs := s.opInputs ++ (t.inputs.map (·, kt.opid, bid)).filter (fun e => !s.opInputs.contains e) }
    s := addGlobals s cid (.transition t) (some bid)
    s := addAssignments s cid (.transition t) (some witness) (some bid)
  return s

/-- Store a seal witness, merging it with a stored copy: a whole tree is kept,
known proofs are joined, a stored SPV proof is kept. -/
def consumeWitness (s : Stock) (w : SealWitness) : Stock :=
  match s.witness? w.tx.txid with
  | some old =>
    let tree := if old.mpcTree.messages.isEmpty then w.mpcTree else old.mpcTree
    let proofs := old.proofs ++ w.proofs.filter fun (c, _) => !(old.proofs.any (·.1 == c))
    { s with witnesses := (s.witnesses.filter (·.tx.txid != w.tx.txid)) ++
      [{ w with mpcTree := tree, proofs, spvProof := old.spvProof <|> w.spvProof }] }
  | none => { s with witnesses := s.witnesses ++ [w] }

/-! ## (In)validation -/

/-- Mark an operation and every operation built on it invalid (`set_ops_as_invalid`). -/
def setOpsInvalid (s : Stock) (op : OpId) : Stock :=
  let rec go (fuel : Nat) (s : Stock) (todo : List OpId) : Stock :=
    match fuel, todo with
    | 0, _ | _, [] => s
    | fuel + 1, o :: rest =>
      if s.invalidOps.contains o then go fuel s rest
      else go fuel { s with invalidOps := s.invalidOps ++ [o] } (rest ++ s.childOps o)
  go (s.opBundle.length + s.opInputs.length + 1) s [op]

/-- Valid again: operations of bundles with a valid witness whose inputs are
valid (`maybe_update_ops_as_valid`), repeated until nothing changes. -/
def revalidate (s : Stock) : Stock :=
  let rec go (fuel : Nat) (s : Stock) : Stock :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      let back := s.invalidOps.filter fun o =>
        match s.bundleOf? o with
        | none => false
        | some b => s.bundleHasValidWitness b &&
          ((s.opInputs.filter fun (_, child, _) => child == o).all fun (i, _, _) => !s.invalidOps.contains i.op)
      if back.isEmpty then s else go fuel { s with invalidOps := s.invalidOps.filter (!back.contains ·) }
  go (s.invalidOps.length + 1) s

/-! ## Accepting consignments -/

/-- Status of a witness: a valid SPV proof gives its mined position, otherwise the resolver. -/
def resolveWitnessOrd (r : Resolver) (l : Layer1) (tx : Tx) (spv : Option SpvProof) :
    Except StockError WitnessOrd := do
  let txid := tx.txid
  if let some p := spv then
    if let .ok h := r.getBlockHeader p.blockHeight then
      if let .ok (some pos) := p.verifiedPos txid h l then return .mined pos
  match r.resolveWitness txid with
  | .error e => throw (.witnessUnresolved txid e)
  | .ok st => return st.witnessOrd

/-- Accept a validated consignment (`consume_consignment`): re-resolve every
witness; a bundle left with no valid witness (and no valid alternative witness in
the stash) refuses the consignment (`absentValidWitness`); otherwise store
genesis, witnesses, bundles and indexes, and revalidate what a reorg had
invalidated. The schema must be imported. -/
def consumeConsignment (s : Stock) (vc : ValidConsignment) (r : Resolver) : Except StockError Stock := do
  let c := vc.consignment
  let cid := c.contractId
  let l := c.genesis.chainNet.layer1
  let mut resolved : List (Txid × WitnessOrd) := []
  for w in c.bundles do
    if !(resolved.any (·.1 == w.witnessId)) then
      let o ← resolveWitnessOrd r l w.tx w.spvProof
      resolved := resolved ++ [(w.witnessId, o)]
  let ordOf (t : Txid) : Option WitnessOrd := ((resolved.find? (·.1 == t)).map (·.2)) <|> s.ord? t
  let stale := c.bundles.filter fun w =>
    !((ordOf w.witnessId).any WitnessOrd.isValid) &&
    !((s.witnessIdsOf w.bundle.bundleId).any fun t => (ordOf t).any WitnessOrd.isValid)
  -- rgb-ops stores the fresh statuses and invalidations before refusing; rgb-lib
  -- runs the call in a savepoint that the error rolls back, so the stash is unchanged
  if !stale.isEmpty then throw .absentValidWitness
  if (s.rules? c.schemaId).isNone then throw (.schemaNotImported c.schemaId)
  let known := (s.secretSeals.map (·.2))
  let c := c.revealSeals known
  let mut s := s.consumeGenesis c.genesis
  for w in c.bundles do
    s := putWitnessOrd s w.witnessId ((ordOf w.witnessId).getD .archived)
    s ← s.consumeBundle cid w.bundle w.witnessId
    s := s.consumeWitness ⟨w.tx, default, w.anchor.dbcProof, w.spvProof, [(cid, w.anchor.mpcProof)]⟩
  return s.revalidate

/-- Consume a fascia (`consume_fascia`): store the witness with the given status
and every bundle; no validation happens here. -/
def consumeFascia (s : Stock) (f : Fascia) (o : WitnessOrd) : Except StockError Stock := do
  let t := f.witnessId
  let mut s := (s.consumeWitness f.sealWitness)
  s := putWitnessOrd s t o
  for (cid, b) in f.bundles.toList do
    if b.checkOpidCommitments.toOption.isNone then throw (.invalidBundle cid b.bundleId)
    if (s.genesis? cid).isNone then throw (.inconsistency (.contractAbsent cid))
    s ← s.consumeBundle cid b t
  return s

/-! ## State -/

/-- A stored allocation is visible: genesis state, or its operation is valid and
its bundle has a valid witness. -/
def rowVisible (s : Stock) (r : AllocRow) : Bool :=
  !s.invalidOps.contains r.opout.op &&
    match r.bundleId with
    | none => true
    | some b => s.bundleHasValidWitness b

/-- Visible allocations with their outpoint: a witness-output seal appears once
per valid witness of its bundle. -/
def allocations (s : Stock) (cid : ContractId) : List (Outpoint × Opout × AllocatedState) :=
  (s.allocs.filter fun r => r.contractId == cid && s.rowVisible r).flatMap fun r =>
    match r.sealTxid, r.bundleId with
    | some t, _ => [(⟨t, r.vout⟩, r.opout, r.state)]
    | none, some b =>
      ((s.witnessIdsOf b).filter fun t => (s.ord? t).any WitnessOrd.isValid).map fun t =>
        (⟨t, r.vout⟩, r.opout, r.state)
    | none, none => []

/-- Visible allocations at given outpoints (`contract_assignments_for`). -/
def allocationsAt (s : Stock) (cid : ContractId) (outpoints : List Outpoint) :
    List (Outpoint × Opout × AllocatedState) :=
  (s.allocations cid).filter fun (o, _, _) => outpoints.contains o

/-- Global values of a type, latest first, cut to the schema limit; values of
bundles without a valid witness are dropped. -/
def globalValues (s : Stock) (cid : ContractId) (ty : GlobalStateType) : List RevealedData :=
  let limit := ((s.genesis? cid).bind fun g => (s.rules? g.schemaId).bind fun r =>
    (r.schema.globalTypes.find? ty).map (·.globalStateSchema.maxItems)).getD 0
  let rows := s.globals.filter fun r => r.contractId == cid && r.ty == ty &&
    match r.bundleId with
    | none => true
    | some b => s.bundleHasValidWitness b
  let sorted := rows.mergeSort fun a b => compare a.ord b.ord != .gt
  (sorted.reverse.take limit).map (·.value)

/-- Contracts with any index entry at the outpoints (no validity filter). -/
def contractsAssigning (s : Stock) (outpoints : List Outpoint) : List ContractId :=
  ((s.outpointOpouts.filter fun (_, o, _) => outpoints.contains o).map (·.1)).eraseDups

/-! ## Witness updates -/

/-- Re-resolve stored witnesses (`update_witnesses`): mined at or above
`afterHeight`, tentative and archived ones (ignored ones are skipped). A change
between archived and valid (in)validates the bundles they anchor. Returns the
new stash and the witnesses whose resolution failed. -/
def updateWitnesses (s : Stock) (r : Resolver) (afterHeight : Nat := 1) : Stock × List Txid :=
  let candidates := s.ords.filter fun (_, o) => match o with
    | .mined p => p.height ≥ max afterHeight 1
    | .tentative | .archived => true
    | .ignored => false
  let (s', failed) := candidates.foldl (fun (acc : Stock × List Txid) (t, old) =>
    let (s, failed) := acc
    match r.resolveWitness t with
    | .error _ => (s, failed ++ [t])
    | .ok st =>
      let o := st.witnessOrd
      let s := putWitnessOrd s t o
      if old.isValid && !o.isValid then
        let s := (s.bundlesOfWitness t).foldl (fun s b =>
          if s.bundleHasValidWitness b then s else (s.opsInBundle b).foldl setOpsInvalid s) s
        (s, failed)
      else (s, failed)) (s, [])
  (s'.revalidate, failed)

/-! ## Composing consignments -/

/-- Height used to order bundles: mined height, tentative and ignored last. -/
def ordHeight : WitnessOrd → Nat
  | .mined p => p.height
  | .tentative => 4294967294
  | .ignored => 4294967295
  | .archived => 4294967295

/-- The witness bundle of a stored bundle, keeping only the requested known
transitions (`witness_bundle` with `to_concealed_except`). -/
def witnessBundle (s : Stock) (cid : ContractId) (bid : BundleId) (opids : List OpId) (w : Txid) :
    Except StockError WitnessBundle := do
  let some b := s.bundle? bid | throw (.inconsistency (.bundleAbsent bid))
  let kts := b.knownTransitions.filter fun kt => opids.contains kt.opid
  if kts.isEmpty then throw (.noRequestedTransition bid)
  let some sw := s.witness? w | throw (.inconsistency (.witnessAbsent w))
  let some a := sw.anchor? cid | throw (.inconsistency (.witnessMissesContract w bid cid))
  return { tx := sw.tx, spvProof := sw.spvProof, anchor := a, bundle := { b with knownTransitions := kts } }

/-- Compose a consignment (`consign`): the operations assigning to `outputs` or
`secrets`, the requested `opids`, and all their ancestors, each in a bundle
anchored by its best valid witness, ordered by height and dependency. -/
def consign (s : Stock) (cid : ContractId) (outputs : List Outpoint) (secrets : List SecretSeal)
    (opids : List OpId) (transfer : Bool) : Except StockError Consignment := do
  let some g := s.genesis? cid | throw (.inconsistency (.contractAbsent cid))
  if (s.rules? g.schemaId).isNone then throw (.schemaNotImported g.schemaId)
  for o in outputs do
    if !(s.outpointOpouts.any fun (c, op, _) => c == cid && op == o) then
      throw (.inconsistency (.outpointUnknown o cid))
  let fromOutputs := (s.outpointOpouts.filter fun (c, o, _) => c == cid && outputs.contains o).map (·.2.2.op)
  let fromSecrets := (s.secretOpouts.filter fun (c, sec, _) => c == cid && secrets.contains sec).map (·.2.2.op)
  let start := (opids ++ fromOutputs ++ fromSecrets).eraseDups.filter (· != g.id)
  -- walk ancestors
  let mut todo := start
  let mut seen : List OpId := []
  let mut fuel := s.opBundle.length + 1
  while fuel > 0 && !todo.isEmpty do
    fuel := fuel - 1
    let o := todo.headD default
    todo := todo.drop 1
    if seen.contains o || o == g.id then continue
    seen := seen ++ [o]
    let some bid := s.bundleOf? o | throw (.inconsistency (.opBundleAbsent o))
    let some b := s.bundle? bid | throw (.inconsistency (.bundleAbsent bid))
    let some t := b.transition? o | throw (.concealed bid o)
    todo := todo ++ t.inputs.map (·.op)
  -- group by bundle, pick witnesses
  let bids := (seen.filterMap s.bundleOf?).eraseDups
  let mut wbs : List (WitnessBundle × Nat) := []
  for bid in bids do
    let ids := s.witnessIdsOf bid
    if ids.isEmpty then throw (.inconsistency (.bundleWitnessUnknown bid))
    let (w, o) ← s.selectValidWitness ids
    let wb ← s.witnessBundle cid bid (seen.filter fun op => s.bundleOf? op == some bid) w
    wbs := wbs ++ [(wb, ordHeight o)]
  -- order: by height, then parents before children
  let sorted := (wbs.mergeSort fun a b => a.2 ≤ b.2).map (·.1)
  let deps (wb : WitnessBundle) : List BundleId :=
    (wb.bundle.knownTransitions.flatMap fun kt => kt.transition.inputs.filterMap fun i => s.bundleOf? i.op)
      |>.filter (· != wb.bundle.bundleId)
  let mut placed : List WitnessBundle := []
  let mut rest := sorted
  let mut fuel2 := sorted.length + 1
  while fuel2 > 0 && !rest.isEmpty do
    fuel2 := fuel2 - 1
    match rest.find? fun wb => (deps wb).all fun d =>
        placed.any (·.bundle.bundleId == d) || !(sorted.any (·.bundle.bundleId == d)) with
    | none => throw .bundlesInconsistency
    | some wb =>
      placed := placed ++ [wb]
      rest := rest.filter (·.bundle.bundleId != wb.bundle.bundleId)
  if !rest.isEmpty then throw .bundlesInconsistency
  return { transfer, genesis := g, bundles := if transfer then placed else [] }

/-- The contract consignment of a contract (`export_contract`). -/
def exportContract (s : Stock) (cid : ContractId) : Except StockError Consignment :=
  s.consign cid [] [] [] false

/-- A transfer whose last bundle comes from a fascia not consumed yet
(`transfer_from_fascia`): the fascia transitions paying `outputs`/`secrets` (or
listed in `opids`) and their ancestors from the stash. -/
def transferFromFascia (s : Stock) (cid : ContractId) (outputs : List Outpoint) (secrets : List SecretSeal)
    (opids : List OpId) (f : Fascia) : Except StockError Consignment := do
  let some b := f.bundles.find? cid | throw (.unrelatedContract cid)
  let w := f.witnessId
  let requested (kt : KnownTransition) : Bool :=
    opids.contains kt.opid || kt.transition.assignments.toList.any fun (_, ta) =>
      ta.items.any fun (bs, _) => match bs.revealed? with
        | some g => outputs.contains (g.outpointOr w)
        | none => secrets.contains bs.toSecret
  let (keep, _) := b.knownTransitions.reverse.foldl (fun (acc : List KnownTransition × List OpId) kt =>
    let (keep, required) := acc
    if required.contains kt.opid || requested kt then
      (kt :: keep, required.filter (· != kt.opid) ++ kt.transition.inputs.map (·.op))
    else (keep, required)) ([], [])
  if keep.isEmpty then throw (.noRequestedTransition b.bundleId)
  let some a := f.sealWitness.anchor? cid | throw (.unrelatedContract cid)
  let last : WitnessBundle := { tx := f.sealWitness.tx, anchor := a, bundle := { b with knownTransitions := keep } }
  let parents := (keep.flatMap fun kt => kt.transition.inputs.map (·.op)).filter fun o =>
    !(keep.any (·.opid == o))
  let base ← s.consign cid [] [] parents true
  return { base with bundles := base.bundles ++ [last] }

end Stock

end Rgb
