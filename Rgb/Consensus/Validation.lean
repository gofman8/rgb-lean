import Rgb.Consensus.Vm
import Rgb.Consensus.Bundle
import Rgb.Consensus.Resolver
import Rgb.Commit.Dbc

/-!
# Consensus validation

Validation runs in two phases.

**Phase 1** reads only the consignment and the schema rules. It checks the chain
network and the schema, then validates genesis and every known transition of
every bundle in consignment order: the transition's id and contract; each input
is mapped to it by the bundle, is a revealed and unspent output of an earlier
operation, and is spent once; the witness transaction spends every input seal
and carries the anchor's commitment to the bundle; the operation fits its schema
(metadata, global state, inputs, assignments and their state types); and its
schema routine accepts it. The first failure ends validation.

**Phase 2** resolves every witness transaction on layer 1 (an SPV proof first,
then the resolver): an unknown or archived witness invalidates the consignment;
a witness above the safe height, or not mined, adds an unsafe-history warning.
Claims that routines pushed (bridge locks) are confirmed by the caller.
-/

namespace Rgb

/-- A schema with the scripts its routines live in (`SchemaRules`). -/
structure SchemaRules where
  schema : Schema
  scripts : List Lib
  deriving DecidableEq, Repr, Inhabited

/-- Why a witness does not close the input seals (`seals::txout::VerifyError`). -/
inductive SealVerifyError where
  | witnessNotClosingSeal (o : Outpoint)
  | noWitnessTxid
  | dbc (e : DbcError)
  deriving DecidableEq, Repr

/-- Validation failures (`Failure`). -/
inductive Failure where
  | contractChainNetMismatch (configured : ChainNet)
  /-- Defined but never emitted. -/
  | resolverChainNetMismatch (c : ChainNet)
  | schemaMismatch (expected actual : SchemaId)
  | schemaGlobalSemIdUnknown (t : GlobalStateType) (sem : SemId)
  | schemaOwnedSemIdUnknown (t : AssignmentType) (sem : SemId)
  | schemaMetaSemIdUnknown (t : MetaType) (sem : SemId)
  | schemaOpEmptyInputs (op : OpFullType)
  | schemaOpMetaTypeUnknown (op : OpFullType) (t : MetaType)
  | schemaOpGlobalTypeUnknown (op : OpFullType) (t : GlobalStateType)
  | schemaOpAssignmentTypeUnknown (op : OpFullType) (t : AssignmentType)
  | schemaUnknownTransitionType (opid : OpId) (t : TransitionType)
  | schemaUnknownMetaType (opid : OpId) (t : MetaType)
  | schemaUnknownGlobalStateType (opid : OpId) (t : GlobalStateType)
  | schemaUnknownAssignmentType (opid : OpId) (t : AssignmentType)
  | schemaGlobalStateOccurrences (opid : OpId) (t : GlobalStateType) (m : OccurrencesMismatch)
  | schemaGlobalStateLimit (opid : OpId) (t : GlobalStateType) (count max : Nat)
  | schemaNoMetadata (opid : OpId) (t : MetaType)
  | schemaInvalidMetadata (opid : OpId) (sem : SemId)
  | schemaInvalidGlobalValue (opid : OpId) (t : GlobalStateType) (sem : SemId)
  | schemaInvalidOwnedValue (opid : OpId) (t : AssignmentType) (sem : SemId)
  | schemaInputOccurrences (opid : OpId) (t : AssignmentType) (m : OccurrencesMismatch)
  | schemaAssignmentOccurrences (opid : OpId) (t : AssignmentType) (m : OccurrencesMismatch)
  | cyclicGraph (o : Opout)
  | contractMismatch (opid : OpId) (c : ContractId)
  | transitionIdMismatch (claimed actual : OpId)
  /-- Defined but never emitted. -/
  | witnessMissingInput (b : BundleId) (o : Outpoint) (t : Txid)
  | inputMapTransitionMismatch (b : BundleId) (opid : OpId) (o : Opout)
  | noPrevState (opid : OpId) (o : Opout)
  | sealNoPubWitness (b : BundleId) (t : Txid)
  | sealsInvalid (b : BundleId) (t : Txid) (e : SealVerifyError)
  | mpcInvalid (b : BundleId) (t : Txid) (e : Mpc.InvalidProof)
  | noDbcOutput (t : Txid)
  | invalidProofType (t : Txid) (m : DbcMethod)
  | stateTypeMismatch (opid : OpId) (t : AssignmentType) (expected found : StateType)
  | scriptFailure (opid : OpId) (errno : Option UInt8)
  | contractStateFilled (opid : OpId)
  | missingScript (opid : OpId) (lib : String)
  | scriptIdMismatch (opid : OpId) (expected actual : String)
  /-- For downstream use; never emitted by consensus. -/
  | custom (s : String)
  deriving DecidableEq, Repr

/-- Warnings: the consignment stays valid (`Warning`). -/
inductive Warning where
  /-- Witnesses above the safe height, by height (0 for unmined ones). -/
  | unsafeHistory (byHeight : List (Nat × List Txid))
  | invalidSpvProof (b : BundleId) (t : Txid)
  | custom (s : String)
  deriving DecidableEq, Repr

/-- Errors of the validation API (`ValidationError`). -/
inductive ValidationError where
  | invalidConsignment (f : Failure)
  | resolverError (e : WitnessResolverError)
  | unknownWitness (t : Txid)
  | unknownClaim
  | pendingClaims (n : Nat)
  deriving DecidableEq, Repr

/-- Validation settings (`ValidationConfig`). -/
structure ValidationConfig where
  chainNet : ChainNet
  /-- Witnesses mined above this height are reported as unsafe history. -/
  safeHeight : Option Nat := none
  buildOpsDag : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- An operation of the history DAG and the opouts it spends, each with the
operation that created it (`OpsDag`). -/
structure DagNode where
  opid : OpId
  spent : List (Opout × OpId)
  deriving DecidableEq, Repr, Inhabited

/-- A witness waiting for layer-1 resolution (`PendingWitness`). -/
structure PendingWitness where
  bundleId : BundleId
  spvProof : Option SpvProof
  ord : Option WitnessOrd
  deriving DecidableEq, Repr, Inhabited

/-- The result of phase 1 (`PendingValidation`). -/
structure PendingValidation where
  warnings : List Warning := []
  opsDag : Option (List DagNode)
  chainNet : ChainNet
  safeHeight : Option Nat
  /-- Witnesses by txid, in ascending txid order. -/
  witnesses : List (Txid × PendingWitness)
  pendingClaims : List Claim
  resolvedClaims : List Claim := []
  unsafeHistory : List (Nat × Txid) := []
  deriving DecidableEq, Repr, Inhabited

/-- Validation status of a valid consignment (`Status`). -/
structure Status where
  warnings : List Warning
  txOrdMap : List (Txid × WitnessOrd)
  opsDag : Option (List DagNode)
  deriving DecidableEq, Repr, Inhabited

/-- Valid, or valid with warnings (`Validity`). -/
inductive Validity where
  | valid
  | warnings
  deriving DecidableEq, Repr

def Status.validity (s : Status) : Validity := if s.warnings.isEmpty then .valid else .warnings

/-! ## Schema rules -/

namespace SchemaRules

/-- Check one operation schema against the schema's declarations (`verify_operation`). -/
def verifyOperation (s : Schema) (op : OpFullType) (metaSchema : OrdSet MetaType)
    (globals : OrdMap GlobalStateType Occurrences) (inputs : Option (OrdMap AssignmentType Occurrences))
    (assignments : OrdMap AssignmentType Occurrences) : Except Failure Unit := do
  for t in metaSchema.toList do
    if !s.metaTypes.contains t then throw (.schemaOpMetaTypeUnknown op t)
  if let some i := inputs then
    if i.isEmpty then throw (.schemaOpEmptyInputs op)
  for t in globals.keys do
    if !s.globalTypes.contains t then throw (.schemaOpGlobalTypeUnknown op t)
  for t in assignments.keys do
    if !s.ownedTypes.contains t then throw (.schemaOpAssignmentTypeUnknown op t)

/-- The schema is consistent (`Schema::verify`); semantic ids of the `other`
kind are unknown to the type system. -/
def verifySchema (s : Schema) : Except Failure Unit := do
  verifyOperation s .genesis s.genesis.metadata s.genesis.globals none s.genesis.assignments
  for (t, d) in s.transitions.toList do
    let ts := d.transitionSchema
    verifyOperation s (.transition t) ts.metadata ts.globals (some ts.inputs) ts.assignments
  let known (sem : SemId) : Bool := match sem with
    | .other _ => false
    | _ => true
  for (t, d) in s.metaTypes.toList do
    if !known d.semId then throw (.schemaMetaSemIdUnknown t d.semId)
  for (t, d) in s.globalTypes.toList do
    if !known d.globalStateSchema.semId then throw (.schemaGlobalSemIdUnknown t d.globalStateSchema.semId)
  for (t, d) in s.ownedTypes.toList do
    match d.ownedStateSchema with
    | .structured sem => if !known sem then throw (.schemaOwnedSemIdUnknown t sem)
    | _ => pure ()

/-- Why a schema definition is refused (`SchemaDefError`). -/
inductive SchemaDefError where
  | scriptAbsent (lib : String)
  | scriptExtraneous (lib : String)
  | schema (f : Failure)
  deriving DecidableEq, Repr

/-- Build checked rules (`SchemaRules::with`): every routine's library is
present, no library is unused, and the schema is consistent. -/
def make (s : Schema) (scripts : List Lib) : Except SchemaDefError SchemaRules := do
  for l in s.libs do
    if !(scripts.any (·.id == l)) then throw (.scriptAbsent l)
  for l in scripts do
    if !(s.libs.contains l.id) then throw (.scriptExtraneous l.id)
  match verifySchema s with
  | .error f => throw (.schema f)
  | .ok () => return ⟨s, scripts⟩

end SchemaRules

/-! ## Phase 1 -/

/-- A spendable output known to the validator: its resolved outpoint and state. -/
structure KnownOpout where
  opout : Opout
  outpoint : Outpoint
  state : RevealedState
  deriving DecidableEq, Repr, Inhabited

/-- Validator state during phase 1. -/
structure ValidatorState where
  /-- Revealed outputs not spent yet in this consignment. -/
  spendable : List KnownOpout := []
  /-- Opouts already used as inputs. -/
  usedInputs : List Opout := []
  /-- Contract global state accumulated so far. -/
  globals : List (GlobalStateType × GlobalEntry) := []
  witnesses : List (Txid × PendingWitness) := []
  claims : List Claim := []
  dag : Option (List DagNode) := none
  deriving Repr, Inhabited

namespace ValidatorState

/-- Contract global values of a type, latest first, cut to the schema limit;
none when the schema has no such type. -/
def contractGlobal (st : ValidatorState) (s : Schema) (t : GlobalStateType) :
    Option (List RevealedData) :=
  (s.globalTypes.find? t).map fun d =>
    let es := (st.globals.filter (·.1 == t)).map (·.2)
    let sorted := es.mergeSort fun a b => compare a.ord b.ord != .gt
    (sorted.reverse.take d.globalStateSchema.maxItems).map (·.value)

def registerOp (st : ValidatorState) (opid : OpId) : ValidatorState :=
  { st with dag := st.dag.map fun d => if d.any (·.opid == opid) then d else d ++ [⟨opid, []⟩] }

/-- Record the revealed outputs of an operation (`process_assignments`); a
concealed seal makes its output unspendable in this consignment. -/
def processAssignments (st : ValidatorState) (op : Operation) (witness : Option Txid) :
    ValidatorState :=
  let st := st.registerOp op.id
  let fresh := op.assignments.toList.flatMap fun (ty, ta) =>
    ta.items.zipIdx.filterMap fun ((bs, state), no) =>
      match bs.revealed?, witness with
      | some s, some w => some ⟨⟨op.id, ty, no.toUInt16⟩, s.outpointOr w, state⟩
      | some s, none => (s.outpoint?).map fun o => ⟨⟨op.id, ty, no.toUInt16⟩, o, state⟩
      | none, _ => none
  let kept := st.spendable.filter fun k => !(fresh.any (·.opout == k.opout))
  { st with spendable := kept ++ fresh }

end ValidatorState

/-- Check an operation against its schema and run its routine
(`SchemaRules::validate_state`). Returns the claims it pushed and the evolved state. -/
def validateState (rules : SchemaRules) (contractId : ContractId) (op : Operation)
    (witness : Option Txid) (prev : OrdMap AssignmentType (List RevealedState))
    (st : ValidatorState) : Except Failure (List Claim × ValidatorState) := do
  let s := rules.schema
  let opid := op.id
  let (metaSchema, globals, inputs, assigns, validator) ← match op with
    | .genesis _ =>
      pure (s.genesis.metadata, s.genesis.globals, (({} : OrdMap AssignmentType Occurrences)),
        s.genesis.assignments, s.genesis.validator)
    | .transition t => match s.transitions.find? t.transitionType with
      | none => throw (.schemaUnknownTransitionType opid t.transitionType)
      | some d =>
        pure (d.transitionSchema.metadata, d.transitionSchema.globals, d.transitionSchema.inputs,
          d.transitionSchema.assignments, d.transitionSchema.validator)
  -- metadata: no unknown type; every listed type present and well typed
  for t in op.metadata.keys do
    if !metaSchema.contains t then throw (.schemaUnknownMetaType opid t)
  for t in metaSchema.toList do
    match op.metadata.find? t with
    | none => throw (.schemaNoMetadata opid t)
    | some v =>
      let sem := ((s.metaTypes.find? t).map (·.semId)).getD (.other "?")
      if !v.v.conforms sem then throw (.schemaInvalidMetadata opid sem)
  -- global state: no unknown type; counts and values per the schema
  for t in op.globals.keys do
    if !globals.contains t then throw (.schemaUnknownGlobalStateType opid t)
  for (t, occ) in globals.toList do
    let vals := (op.globals.find? t).getD []
    match occ.check vals.length with
    | .error m => throw (.schemaGlobalStateOccurrences opid t m)
    | .ok () => pure ()
    let gs := ((s.globalTypes.find? t).map (·.globalStateSchema)).getD ⟨.other "?", 0⟩
    if vals.length > gs.maxItems then throw (.schemaGlobalStateLimit opid t vals.length gs.maxItems)
    for v in vals do
      if !v.v.conforms gs.semId then throw (.schemaInvalidGlobalValue opid t gs.semId)
  -- spent state: only listed types, in the listed numbers
  for t in prev.keys do
    if !inputs.contains t then throw (.schemaUnknownAssignmentType opid t)
  for (t, occ) in inputs.toList do
    match occ.check ((prev.find? t).getD []).length with
    | .error m => throw (.schemaInputOccurrences opid t m)
    | .ok () => pure ()
  -- new state: only listed types, in the listed numbers, of the declared kind
  let own := op.assignments
  for t in own.keys do
    if !assigns.contains t then throw (.schemaUnknownAssignmentType opid t)
  for (t, occ) in assigns.toList do
    let ta? := own.find? t
    match occ.check ((ta?.map TypedAssigns.len).getD 0) with
    | .error m => throw (.schemaAssignmentOccurrences opid t m)
    | .ok () => pure ()
    if let some ta := ta? then
      let oss := ((s.ownedTypes.find? t).map (·.ownedStateSchema)).getD .declarative
      for (_, state) in ta.items do
        match oss, state with
        | .declarative, .void => pure ()
        | .fungible _, .fungible _ => pure ()
        | .structured sem, .structured d =>
          if !d.v.conforms sem then throw (.schemaInvalidOwnedValue opid t sem)
        | _, _ => throw (.stateTypeMismatch opid t oss.stateType state.stateType)
  -- the routine
  let claims ← match validator with
    | none => pure []
    | some site => match rules.scripts.find? (·.id == site.lib) with
      | none => throw (.missingScript opid site.lib)
      | some lib =>
        let ctx : VmContext := ⟨contractId, opid, op, witness, prev, st.contractGlobal s⟩
        let init : VmState := match op with
          | .transition t => ({} : VmState).set .a16 0 (some t.transitionType.v.toNat)
          | .genesis _ => {}
        let r := lib.run site.offset ctx init
        if r.ok then pure r.claims else throw (.scriptFailure opid r.errno)
  -- evolve the contract state
  return (claims, { st with globals := st.globals ++ op.globalEntries witness })

/-- The witness closes every input seal and commits to the bundle (`validate_seal_closing`). -/
def validateSealClosing (contractId : ContractId) (bundleId : BundleId) (tx : Tx) (anchor : Anchor)
    (seals : List Outpoint) : Except Failure Unit := do
  let txid := tx.txid
  let commitment ← match anchor.mpcProof.convolve contractId bundleId with
    | .error e => throw (.mpcInvalid bundleId txid e)
    | .ok c => pure c
  match dbcOutput? tx with
  | none => throw (.noDbcOutput txid)
  | some (_, m) => if anchor.dbcProof.method != m then throw (.invalidProofType txid anchor.dbcProof.method)
  for o in seals.mergeSort (fun a b => compare a b != .gt) do
    if !tx.spends o then throw (.sealsInvalid bundleId txid (.witnessNotClosingSeal o))
  match anchor.dbcProof.verify commitment tx with
  | .error e => throw (.sealsInvalid bundleId txid (.dbc e))
  | .ok () => pure ()

/-- Validate one known transition of a bundle (`validate_transition`). -/
def validateTransition (rules : SchemaRules) (contractId : ContractId) (bundle : TransitionBundle)
    (tx : Tx) (anchor : Anchor) (kt : KnownTransition) (st : ValidatorState) :
    Except Failure ValidatorState := do
  let t := kt.transition
  let opid := kt.opid
  if opid != t.id then throw (.transitionIdMismatch opid t.id)
  if t.contractId != contractId then throw (.contractMismatch opid t.contractId)
  let bundleId := bundle.bundleId
  let mut st := st
  let mut seals : List Outpoint := []
  let mut prev : OrdMap AssignmentType (List RevealedState) := {}
  for input in t.inputs.mergeSort (fun a b => compare a b != .gt) do
    if bundle.inputMap.find? input != some opid then
      throw (.inputMapTransitionMismatch bundleId opid input)
    match st.spendable.find? (·.opout == input) with
    | none => throw (.noPrevState opid input)
    | some k =>
      st := { st with spendable := st.spendable.filter (·.opout != input) }
      seals := seals ++ [k.outpoint]
      prev := prev.alter input.ty fun l => l.getD [] ++ [k.state]
    if st.usedInputs.contains input then throw (.cyclicGraph input)
    st := { st with usedInputs := st.usedInputs ++ [input] }
  validateSealClosing contractId bundleId tx anchor seals
  let (claims, st') ← validateState rules contractId (.transition t) (some tx.txid) prev st
  return { st' with claims := st'.claims ++ claims }

/-- Add a transition's spent opouts to the DAG (`connect_transition`). -/
def connectTransition (d : List DagNode) (kt : KnownTransition) : List DagNode :=
  let spent := kt.transition.inputs.map fun i => (i, i.op)
  if d.any (·.opid == kt.opid) then
    d.map fun n => if n.opid == kt.opid then { n with spent := n.spent ++ spent } else n
  else d ++ [⟨kt.opid, spent⟩]

/-- The data validation reads from a consignment (`ConsignmentApi`): genesis and,
per witness bundle, the bundle, its anchor, the witness transaction and an
optional SPV proof. -/
structure ConsensusInput where
  genesis : Genesis
  bundles : List (TransitionBundle × Anchor × Tx × Option SpvProof)
  deriving Repr, Inhabited

/-- Phase 1 (`Validator::validate_deterministic`). -/
def validateDeterministic (rules : SchemaRules) (c : ConsensusInput) (cfg : ValidationConfig) :
    Except ValidationError PendingValidation :=
  let g := c.genesis
  let cid := g.contractId
  let wrap {α : Type} (r : Except Failure α) : Except ValidationError α := r.mapError .invalidConsignment
  do
    if g.chainNet != cfg.chainNet then throw (.invalidConsignment (.contractChainNetMismatch cfg.chainNet))
    if rules.schema.schemaId != g.schemaId then
      throw (.invalidConsignment (.schemaMismatch g.schemaId rules.schema.schemaId))
    let st0 : ValidatorState := { dag := if cfg.buildOpsDag then some [] else none }
    let (claims, stG) ← wrap (validateState rules cid (.genesis g) none {} st0)
    let mut st := { (stG.processAssignments (.genesis g) none) with claims := claims }
    for (bundle, anchor, tx, spv) in c.bundles do
      let txid := tx.txid
      if !(st.witnesses.any (·.1 == txid)) then
        st := { st with witnesses := st.witnesses ++ [(txid, ⟨bundle.bundleId, spv, none⟩)] }
      for kt in bundle.knownTransitions do
        st ← wrap (validateTransition rules cid bundle tx anchor kt st)
        st := st.processAssignments (.transition kt.transition) (some txid)
        st := { st with dag := st.dag.map (connectTransition · kt) }
    let ws := st.witnesses.mergeSort fun a b => compare a.1 b.1 != .gt
    return { opsDag := st.dag, chainNet := cfg.chainNet, safeHeight := cfg.safeHeight
             witnesses := ws, pendingClaims := st.claims.eraseDups }

/-! ## Phase 2 -/

namespace PendingValidation

/-- Resolve one witness: a valid SPV proof gives its mined position without
asking the resolver; otherwise the resolver must find it and not archive it. -/
def resolveTask (r : Resolver) (l : Layer1) (txid : Txid) (w : PendingWitness) :
    Except ValidationError (WitnessOrd × Option Warning) := do
  let mut warning : Option Warning := none
  if let some p := w.spvProof then
    match r.getBlockHeader p.blockHeight with
    | .ok h =>
      match p.verifiedPos txid h l with
      | .ok (some pos) => return (.mined pos, none)
      | _ => warning := some (.invalidSpvProof w.bundleId txid)
    | .error .notSupported => pure ()
    | .error e => throw (.resolverError e)
  match r.resolveWitness txid with
  | .error e => throw (.resolverError e)
  | .ok .unresolved => throw (.invalidConsignment (.sealNoPubWitness w.bundleId txid))
  | .ok (.resolved tx ord) =>
    if tx.txid != txid then throw (.resolverError (.idMismatch tx.txid txid))
    if ord == .archived then throw (.invalidConsignment (.sealNoPubWitness w.bundleId txid))
    return (ord, warning)

/-- Record a witness status; with a safe height, a witness mined above it or not
mined is unsafe history (`resolve_witness`). -/
def recordWitness (pv : PendingValidation) (txid : Txid) (ord : WitnessOrd) (warning : Option Warning) :
    Except ValidationError PendingValidation := do
  let some (_, w) := pv.witnesses.find? (·.1 == txid) | throw (.unknownWitness txid)
  if ord == .archived then throw (.invalidConsignment (.sealNoPubWitness w.bundleId txid))
  let witnesses := pv.witnesses.map fun (t, p) => if t == txid then (t, { p with ord := some ord }) else (t, p)
  let unsafeNew := match pv.safeHeight, ord with
    | some sh, .mined pos => if pos.height > sh then [(pos.height, txid)] else []
    | some _, _ => [(0, txid)]
    | none, _ => []
  return { pv with witnesses, unsafeHistory := pv.unsafeHistory ++ unsafeNew
                   warnings := pv.warnings ++ warning.toList }

/-- Resolve every unresolved witness, in ascending txid order (`resolve_all`). -/
def resolveAll (pv : PendingValidation) (r : Resolver) : Except ValidationError PendingValidation := do
  match r.checkChainNet pv.chainNet with
  | .error e => throw (.resolverError e)
  | .ok () => pure ()
  let mut pv := pv
  for (txid, w) in pv.witnesses do
    if w.ord.isNone then
      let (ord, warning) ← resolveTask r pv.chainNet.layer1 txid w
      pv ← pv.recordWitness txid ord warning
  return pv

/-- Mark a claim confirmed (`resolve_claim`). -/
def resolveClaim (pv : PendingValidation) (c : Claim) : Except ValidationError PendingValidation :=
  if pv.resolvedClaims.contains c then .ok pv
  else if pv.pendingClaims.contains c then
    .ok { pv with pendingClaims := pv.pendingClaims.filter (· != c), resolvedClaims := pv.resolvedClaims ++ [c] }
  else .error .unknownClaim

def isResolved (pv : PendingValidation) : Bool :=
  pv.witnesses.all (·.2.ord.isSome) && pv.pendingClaims.isEmpty

/-- Final status; unsafe history becomes a warning (`finalize`). -/
def finalize (pv : PendingValidation) : Status :=
  let heights := (pv.unsafeHistory.map (·.1)).eraseDups
  let byHeight := heights.map fun h => (h, (pv.unsafeHistory.filter (·.1 == h)).map (·.2))
  let ws := if pv.safeHeight.isSome && !pv.unsafeHistory.isEmpty then pv.warnings ++ [.unsafeHistory byHeight]
    else pv.warnings
  { warnings := ws, txOrdMap := pv.witnesses.filterMap fun (t, w) => w.ord.map (t, ·), opsDag := pv.opsDag }

end PendingValidation

/-- Full validation with a witness resolver and no claim resolver
(`Validator::validate`): a routine that pushed a claim makes it fail. -/
def validate (rules : SchemaRules) (c : ConsensusInput) (r : Resolver) (cfg : ValidationConfig) :
    Except ValidationError Status := do
  let pv ← validateDeterministic rules c cfg
  let pv ← pv.resolveAll r
  if !pv.pendingClaims.isEmpty then throw (.pendingClaims pv.pendingClaims.length)
  return pv.finalize

end Rgb
