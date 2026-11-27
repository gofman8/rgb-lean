import Rgb.Lib.Evm
import Rgb.Lib.SchemaMap
import Rgb.Ops.Witness

/-!
# Validation, inspection and SPV proofs without a wallet

The `no_wallet` API of rgb-lib. `validate_consignment_with_resolver` takes the caller's
witness, claim and reject list resolvers; `validate_consignment` builds them from an
indexer, EVM RPC URLs and HTTP. Both check a consignment file in this order, the first
failure winning:

1. the path exists (`invalidFilePath`);
2. the offchain TXID, if given, reads as a txid (`invalidTxid`);
3. the file is a transfer or a contract consignment (`invalidConsignment`);
4. the offchain TXID is the id of a bundled witness (`offchainTxidNotFound`);
5. rgb-lib knows the schema (`unknownRgbSchema`);
6. phase 1 of consensus validation passes (`consignmentValidationFailed`);
7. the claims the routines pushed (BFA mint locks) are confirmed on the bridge's chain;
8. phase 2 resolves every witness, the offchain one from the consignment as tentative;
9. the terminal operations pass the asset's reject list (`consignmentRejected`).

Inspection reads a consignment, or a fascia and its PSBT, without validating them.
`fill_spv_proofs` adds the SPV proofs an indexer has for the witnesses that lack one.

The model shows an id as the eight hex digits of its `Digest.short` and reads id texts in
that form. Error details that carry a consensus failure, a resolver error or a decoding
error hold the model's rendering of it.
-/

namespace Rgb.Lib.NoWallet

open Rgb.Lib.Evm

/-! ## Results -/

/-- Options of the validation functions (`ValidationOptions`). -/
structure ValidationOptions where
  /-- Network the consignment must be for. -/
  bitcoinNetwork : BitcoinNetwork
  /-- TXID of a witness taken from the consignment, as it may not be broadcast yet. -/
  offchainTxid : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- Status of a validated witness (`WitnessValidationStatus`). -/
inductive WitnessValidationStatus where
  | mined (height : Nat) (timestamp : Int)
  | tentative
  | ignored
  | archived
  deriving DecidableEq, Repr

/-- The status of a witness order. -/
def WitnessValidationStatus.ofOrd : WitnessOrd → WitnessValidationStatus
  | .mined pos => .mined pos.height pos.timestamp
  | .tentative => .tentative
  | .ignored => .ignored
  | .archived => .archived

/-- A witness of a validated consignment (`ValidatedWitness`). -/
structure ValidatedWitness where
  txid : String
  status : WitnessValidationStatus
  /-- Taken from the consignment as the offchain witness, not checked against the chain. -/
  fromConsignment : Bool
  deriving DecidableEq, Repr

/-- A warning of a validated consignment (`ValidationWarning`). -/
inductive ValidationWarning where
  /-- Witnesses mined above the safe height or not mined, sorted. -/
  | unsafeHistory (txids : List String)
  /-- The bundle's SPV proof does not verify; its witness was resolved without it. -/
  | invalidSpvProof (bundleId txid : String)
  | other (details : String)
  deriving DecidableEq, Repr

/-- Strings in ascending order. -/
def sortStrings (l : List String) : List String := l.mergeSort fun a b => compare a b != .gt

/-- The warning rgb-lib reports for a consensus warning. -/
def ValidationWarning.ofWarning : Warning → ValidationWarning
  | .unsafeHistory byHeight => .unsafeHistory (sortStrings ((byHeight.flatMap (·.2)).map toString))
  | .invalidSpvProof b t => .invalidSpvProof (toString b) (toString t)
  | .custom s => .other s

/-- Result of validating a consignment (`ConsignmentValidation`), for a valid one only. -/
structure ConsignmentValidation where
  consignmentId : String
  /-- False for a contract consignment. -/
  isTransfer : Bool
  assetId : String
  assetSchema : AssetSchema
  /-- Height the witnesses were checked against; none when no confirmation policy applies. -/
  safeHeight : Option Nat
  /-- Witnesses sorted by TXID. -/
  witnesses : List ValidatedWitness
  warnings : List ValidationWarning
  deriving DecidableEq, Repr

/-- The report of a valid consignment (`ConsignmentValidation::new`). -/
def ConsignmentValidation.ofStatus (c : Consignment) (isTransfer : Bool) (schema : AssetSchema)
    (st : Status) (safeHeight : Option Nat) (offchain : Option Txid) : ConsignmentValidation where
  consignmentId := toString c.consignmentId
  isTransfer
  assetId := toString c.contractId
  assetSchema := schema
  safeHeight
  witnesses := (st.txOrdMap.map fun (t, o) =>
      ({ txid := toString t, status := .ofOrd o, fromConsignment := offchain == some t }
        : ValidatedWitness)).mergeSort fun a b => compare a.txid b.txid != .gt
  warnings := st.warnings.map ValidationWarning.ofWarning

/-! ## Ids and schemas -/

/-- Read an id text (`Txid::from_str`, `OpId::from_str`): eight hex digits in either case;
the lowercase form is the text of the id. -/
def idText? (s : String) : Option String :=
  if s.length == 8 && s.toList.all Hex.isDigit then some s.toLower else none

/-- Read a decimal `u16` (`u16::from_str`): an optional `+`, then digits. -/
def parseU16? (s : String) : Option Nat :=
  let ds := (if s.startsWith "+" then (s.drop 1).toString else s).toList
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let v := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if v ≤ 0xFFFF then some v else none

/-- Read `<opid>/<ty>/<no>` (`Opout::from_str`), naming an operation of `known` by its text;
a well-formed opid that names none of them reads as an operation of no consignment. -/
def parseOpout? (known : List OpId) (s : String) : Option Opout :=
  match s.splitOn "/" with
  | [op, ty, no] => do
    let t ← idText? op
    let ty ← parseU16? ty
    let no ← parseU16? no
    let opid := (known.find? (toString · == t)).getD ⟨Digest.of "rgb:opid-text" [t]⟩
    pure ⟨opid, ⟨ty.toUInt16⟩, no.toUInt16⟩
  | _ => none

/-! ## Genesis globals -/

/-- First value of a genesis global. -/
def firstGlobal? (g : Genesis) (t : GlobalStateType) : Option StrictValue :=
  ((g.globals.find? t).bind (·.head?)).map (·.v)

/-- The bridge location a BFA genesis commits to (`BridgedFungibleAsset::bridge_location`). -/
def bridgeLocation (g : Genesis) : Except String BridgeLocation :=
  match firstGlobal? g Schemas.gsBridgeLocation with
  | none => .error "genesis has no `bridgeLocation` global state"
  | some v =>
    match v with
    | .bridgeLocation l => if v.wellFormed then .ok l else .error invalid
    | _ => .error invalid
where
  invalid : String := "genesis global state `bridgeLocation` is not a valid bridge location"

/-- Where an asset's reject list is published (`genesis_reject_list_source`): the first value
of `rejectList` for BFA, of `rejectListUrl` for IFA; the other schemas have none. -/
def genesisRejectListSource (s : AssetSchema) (g : Genesis) :
    Except String (Option RejectListSource) :=
  match s with
  | .bfa =>
    match firstGlobal? g Schemas.gsRejectList with
    | none => .ok none
    | some v =>
      match v with
      | .rejectListLocation (.url u) => if v.wellFormed then .ok (some (.url u.s)) else bad v
      | .rejectListLocation (.evm c) => if v.wellFormed then .ok (some (.evm c)) else bad v
      | _ => bad v
  | .ifa =>
    match firstGlobal? g Schemas.gsRejectListUrl with
    | none => .ok none
    | some v =>
      match v with
      | .rejectListUrl u => if v.wellFormed then .ok (some (.url u.s)) else bad v
      | _ => bad v
  | .nia | .uda | .cfa => .ok none
where
  bad (v : StrictValue) : Except String (Option RejectListSource) :=
    .error s!"cannot decode a {reprStr v.semId} value"

/-! ## Phase 1 and claims -/

/-- `validation_error`: an invalid consignment fails validation, a resolver failure is a
network error, anything else is internal. -/
def validationError : ValidationError → Error
  | .invalidConsignment f => .consignmentValidationFailed (reprStr f)
  | .resolverError e => .network (reprStr e)
  | e => .internal s!"unexpected consignment validation error: {reprStr e}"

/-- How claims are confirmed (`ClaimResolution`). -/
inductive ClaimResolution where
  /-- With the caller's resolver, if any. -/
  | resolver (r : Option ClaimResolver)
  /-- With the node at the URL configured for the bridge's chain. -/
  | evm (urls : EvmRpcUrls) (net : EvmNet)

/-- The caller's resolver as validation uses it: it never reports a mint expired. -/
def customResolver (r : ClaimResolver) : ClaimResolver :=
  { r with isConfirmed := fun ex loc c => (r.isConfirmed ex loc c).map fun (ok, _) => (ok, ex) }

/-- The claims still to confirm, in `Claim` order (`unresolved_claims`). -/
def unresolvedClaims (pv : PendingValidation) : List Claim :=
  pv.pendingClaims.mergeSort fun a b => compare a b != .gt

/-- `resolve_claims`: confirm each claim in order. A mint the resolver found expired stops at
once with `mintLockExpired`; the opids of the other unconfirmed claims are returned. -/
def resolveClaims (pv : PendingValidation) (r : CheckedClaimResolver) (claims : List Claim) :
    Except Error (PendingValidation × List OpId) := do
  let mut pv := pv
  let mut unconfirmed : List OpId := []
  let mut expired : List OpId := []
  for c in claims do
    let (ok, ex) ← (r.isConfirmed expired c).mapError ClaimResolverError.toError
    expired := ex
    if ok then
      match pv.resolveClaim c with
      | .ok pv' => pv := pv'
      | .error e => throw (ClaimResolverError.validation e).toError
    else if expired.contains c.opid then
      throw (.mintLockExpired (toString c.opid) c.beforeBlock.toNat)
    else
      unconfirmed := unconfirmed ++ [c.opid]
  return (pv, unconfirmed)

/-- Phase 1, then the claims (`validate_with_claims`): the first claim left unconfirmed fails
with `mintLockNotFound`. -/
def validateWithClaims (c : Consignment) (expectTransfer : Bool) (schema : AssetSchema)
    (claims : ClaimResolution) (cfg : ValidationConfig) : Except Error PendingValidation := do
  let pv ← (c.validateDeterministic expectTransfer schema.rules cfg).mapError validationError
  let pending := unresolvedClaims pv
  if pending.isEmpty then return pv
  if !schema.supportsMint then
    throw (.consignmentValidationFailed s!"{schema.name} schema does not support claims")
  let location ← (bridgeLocation c.genesis).mapError fun e =>
    .internal s!"unexpected bridge location error: {e}"
  let resolver ← match claims, location with
    | .resolver none, _ => throw .noClaimResolver
    | .resolver (some r), _ => pure (customResolver r)
    | .evm urls net, .evm contract =>
      match urls.lookup contract.chainId.toNat with
      | none => throw (.noEvmRpcUrl contract.chainId.toNat)
      | some url => pure (mintClaimResolver (net url))
  let checked ← (CheckedClaimResolver.check resolver location).mapError
    ClaimResolverError.toError
  let (pv, unconfirmed) ← resolveClaims pv checked pending
  if let some opid := unconfirmed.head? then throw (.mintLockNotFound (toString opid))
  return pv

/-! ## Phase 2 -/

/-- `OffchainResolver`: the witness `offchain` comes from the consignment as tentative; every
other witness, the block headers and the network check come from `fallback`. -/
def offchainResolver (c : Consignment) (offchain : Option Txid) (fallback : Resolver) :
    Resolver :=
  { fallback with resolveWitness := fun t =>
      if offchain != some t then fallback.resolveWitness t
      else match c.bundles.find? (·.witnessId == t) with
        | some wb => .ok (.resolved wb.tx .tentative)
        | none => fallback.resolveWitness t }

/-- Phase 2 (`resolve_witnesses`): resolve every witness, then finalize. -/
def resolveWitnesses (pv : PendingValidation) (r : Resolver) : Except Error Status := do
  let pv ← (pv.resolveAll r).mapError validationError
  return pv.finalize

/-! ## Reject lists -/

/-- A reject list resolver (`ResolveRejectList`): it fetches a list as published. -/
structure RejectListResolver where
  /-- The body served at a URL. -/
  getUrlRejectList : String → Except Error String
  /-- The entries of a reject list contract. -/
  getEvmRejectList : EvmContract → Except Error EvmRejectList

/-- Details of a refused list. -/
def rejectListErrorText : RejectListError → String
  | .finalizedOutOfRange f n => s!"{f} finalized entries reported out of {n}"
  | .invalidOpout s => s!"invalid opout {s}"
  | .unsupportedScheme s => s!"unsupported reject list URL scheme: {s}"
  | .tooLarge => s!"reject list too large: more than {maxRejectListSize} bytes"
  | .notAscii => "reject list is not ASCII"
  | .httpStatus c => s!"reject list request failed: HTTP {c}"

/-- Read a reject list from its source (`RejectList::resolve`), with the number of invalid
lines of a URL list; `known` are the operations opid texts name. -/
def resolveRejectList (r : RejectListResolver) (known : List OpId) (src : RejectListSource) :
    Except Error (RejectList × Nat) := do
  match src with
  | .url u => return RejectList.parse (parseOpout? known) (← r.getUrlRejectList u)
  | .evm c =>
    match RejectList.fromEvm (parseOpout? known) (← r.getEvmRejectList c) with
    | .ok l => return (l, 0)
    | .error e => throw (.invalidRejectList (rejectListErrorText e))

/-- What each URL serves: an HTTP status and a body, or why the request was not sent. -/
abbrev Web := String → Except String (Nat × String)

/-- Scheme of a URL, lowercase: a letter, then letters, digits, `+`, `-` or `.`, before `:`. -/
def urlScheme? (url : String) : Option String :=
  match url.splitOn ":" with
  | s :: _ :: _ =>
    match s.toList with
    | c :: cs =>
      if c.isAlpha && cs.all (fun c => c.isAlphanum || "+-.".toList.contains c) then
        some s.toLower
      else none
    | [] => none
  | _ => none

/-- `RejectListClient::new` and `get_reject_list`: only `http` and `https`, a 2xx answer,
at most `maxRejectListSize` bytes, ASCII. -/
def fetchUrlRejectList (web : Web) (url : String) : Except Error String := do
  let some scheme := urlScheme? url | throw (.rejectListService "relative URL without a base")
  if scheme != "http" && scheme != "https" then
    throw (.rejectListService (rejectListErrorText (.unsupportedScheme scheme)))
  let (status, body) ← (web url).mapError .rejectListService
  (checkRejectListBody status body).mapError fun e => .rejectListService (rejectListErrorText e)

/-- `RemoteRejectListResolver`: URL lists over HTTP, contract lists through the URL of their
chain, whose node is checked to be on it unless the wallet checked it going online. -/
def remoteRejectListResolver (web : Web) (net : EvmNet) (urls : EvmRpcUrls)
    (chainsChecked : Bool) : RejectListResolver where
  getUrlRejectList := fetchUrlRejectList web
  getEvmRejectList := readEvmRejectList net urls chainsChecked

/-- `reject_check_origins`: the inputs and the outputs of the terminal operations, the ones
nothing in the consignment builds on. Other unspent outputs are not checked. -/
def rejectCheckOrigins (c : Consignment) : List Opout :=
  let terminal := c.terminalOps
  let opouts := (c.bundles.flatMap (·.bundle.knownTransitions)).flatMap fun kt =>
    if terminal.contains kt.opid then
      kt.transition.inputs ++ kt.transition.assignments.toList.flatMap fun (ty, ta) =>
        (List.range ta.len).map fun no => ⟨kt.opid, ty, no.toUInt16⟩
    else []
  opouts.eraseDups

/-- `check_reject_list`: an asset with a reject list fetches it even for a contract
consignment, which has no origin to check. -/
def checkRejectList (schema : AssetSchema) (g : Genesis) (dag : Option (List Rgb.DagNode))
    (getList : RejectListSource → Except Error RejectList) (origins : List Opout) :
    Except Error Unit := do
  let source ← (genesisRejectListSource schema g).mapError fun e =>
    .internal s!"invalid reject list in a validated genesis: {e}"
  let some src := source | return ()
  let list ← getList src
  let some dag := dag | throw (.internal "no operations DAG to check against the reject list")
  let nodes : List Rgb.Lib.DagNode := dag.map fun n => ⟨n.opid, n.spent⟩
  if origins.any fun o => !list.allows o && !list.rejects o && !nodes.any (·.opid == o.op) then
    throw (.internal "opout not found in DAG")
  let rejected := rejectedOpouts nodes list origins
  if !rejected.isEmpty then throw (.consignmentRejected (sortStrings (rejected.map toString)))

/-! ## Validation -/

/-- What a path holds, as the loaders read it. -/
inductive ConsignmentFile where
  /-- Nothing. -/
  | missing
  /-- A transfer consignment. -/
  | transfer (c : Consignment)
  /-- A contract consignment. -/
  | contract (c : Consignment)
  /-- A validated transfer or contract consignment (another file type). -/
  | validated (transfer : Bool) (c : Consignment)
  /-- A schema definition, or bytes that do not decode. -/
  | other
  deriving DecidableEq, Repr

/-- `validate_loaded_consignment`: the offchain witness, the schema, phase 1 and claims,
phase 2, then the reject list. -/
def validateLoaded (c : Consignment) (expectTransfer : Bool) (resolver : Resolver)
    (claims : ClaimResolution) (rl : Option RejectListResolver) (safeHeight : Option Nat)
    (offchainText : Option String) (opts : ValidationOptions) :
    Except Error ConsignmentValidation := do
  let offchain ← match offchainText with
    | none => pure none
    | some t =>
      match c.bundles.find? (toString ·.witnessId == t) with
      | some wb => pure (some wb.witnessId)
      | none => throw (.offchainTxidNotFound t)
  let some schema := AssetSchema.ofSchemaId? c.schemaId
    | throw (.unknownRgbSchema (toString c.schemaId))
  let cfg : ValidationConfig := { chainNet := opts.bitcoinNetwork.chainNet, safeHeight
                                  buildOpsDag := schema.supportsRejectList }
  let pv ← validateWithClaims c expectTransfer schema claims cfg
  let st ← resolveWitnesses pv (offchainResolver c offchain resolver)
  let known := c.genesis.id :: c.bundles.flatMap fun wb => wb.bundle.knownTransitions.map (·.opid)
  let getList (src : RejectListSource) : Except Error RejectList := do
    let some r := rl | throw .noRejectListResolver
    return (← resolveRejectList r known src).1
  checkRejectList schema c.genesis st.opsDag getList (rejectCheckOrigins c)
  return .ofStatus c expectTransfer schema st safeHeight offchain

/-- `validate_consignment_file`: the path, the offchain TXID text, the file type, then the
loaded consignment. -/
def validateFile (path : String) (file : ConsignmentFile) (resolver : Resolver)
    (claims : ClaimResolution) (rl : Option RejectListResolver) (safeHeight : Option Nat)
    (opts : ValidationOptions) : Except Error ConsignmentValidation := do
  match file with
  | .missing => throw (.invalidFilePath path)
  | _ => pure ()
  let offchainText ← match opts.offchainTxid with
    | none => pure none
    | some s =>
      match idText? s with
      | some t => pure (some t)
      | none => throw .invalidTxid
  match file with
  | .transfer c => validateLoaded c true resolver claims rl safeHeight offchainText opts
  | .contract c => validateLoaded c false resolver claims rl safeHeight offchainText opts
  | _ => throw .invalidConsignment

/-- `validate_consignment_with_resolver`: the caller's resolvers and safe height (positive);
a missing claim or reject list resolver fails only when it is needed. -/
def validateConsignmentWithResolver (path : String) (file : ConsignmentFile)
    (resolver : Resolver) (claimResolver : Option ClaimResolver)
    (rejectListResolver : Option RejectListResolver) (safeHeight : Option Nat)
    (opts : ValidationOptions) : Except Error ConsignmentValidation :=
  validateFile path file resolver (.resolver claimResolver) rejectListResolver safeHeight opts

/-- What `validate_consignment` and `fill_spv_proofs` reach through an indexer config. -/
structure Indexer where
  /-- Witness resolver (`get_resolver`). -/
  resolver : Resolver
  /-- Latest block height. -/
  tip : Except Error Nat
  /-- SPV proof of a mined witness (`resolve_spv_proof`). -/
  resolveSpvProof : Txid → Except WitnessResolverError SpvProof

/-- An indexer over the simulated chain. -/
def chainIndexer (c : Chain) (net : ChainNet) : Indexer where
  resolver := c.resolver net
  tip := .ok c.height
  resolveSpvProof t :=
    match c.spvProof? t with
    | some p => .ok p
    | none => .error (.resolverIssue (some t) "transaction not mined")

/-- The safe height for `minConfirmations` at tip `tip`, never below 1: a witness mined at it
has exactly `minConfirmations` confirmations and is safe. -/
def safeHeightFor (tip minConfirmations : Nat) : Nat := tip - minConfirmations + 1

/-- `validate_consignment`: claims go through the EVM node of the bridge's chain, reject lists
over HTTP or through the EVM node of the list's chain, checked to be on it. -/
def validateConsignment (path : String) (file : ConsignmentFile) (indexer : Indexer)
    (net : EvmNet) (web : Web) (urls : EvmRpcUrls) (minConfirmations : Option Nat)
    (opts : ValidationOptions) : Except Error ConsignmentValidation := do
  match indexer.resolver.checkChainNet opts.bitcoinNetwork.chainNet with
  | .error e => throw (.invalidIndexer (reprStr e))
  | .ok () => pure ()
  let safeHeight ← match minConfirmations with
    | none => pure none
    | some m => do pure (some (safeHeightFor (← indexer.tip) m))
  validateFile path file indexer.resolver (.evm urls net)
    (some (remoteRejectListResolver web net urls false)) safeHeight opts

/-! ## Inspection results -/

/-- An operation output as inspection shows it (`no_wallet::Opout`). -/
structure OpoutInfo where
  opid : String
  assignmentType : TypeOfAssignment
  index : Nat
  deriving DecidableEq, Repr

/-- An input of a transition (`RgbInputInfo`); `vin` and `assignment` are none when the
spent allocation is not resolved. -/
structure RgbInputInfo where
  opout : OpoutInfo
  vin : Option Nat
  assignment : Option Assignment
  deriving DecidableEq, Repr

/-- An output of an operation (`RgbOutputInfo`). -/
structure RgbOutputInfo where
  /-- Revealed seals only, as are `vout` and `blinding`. -/
  txid : Option String
  vout : Option Nat
  blinding : Option UInt64
  assignment : Assignment
  isConcealed : Bool
  /-- Concealed seals only: the blinded receive the output pays. -/
  recipientId : Option String
  /-- None without a wallet. -/
  isOurs : Option Bool
  /-- Whether the operation is terminal in the consignment; none outside a consignment. -/
  isTerminal : Option Bool
  deriving DecidableEq, Repr

/-- A global value of a transition (`TransitionGlobal`). -/
inductive TransitionGlobal where
  | issuedSupply (n : Nat)
  | burnedAsset (n : Nat)
  | burnedInflation (n : Nat)
  /-- Hex of the 32 bytes. -/
  | burnReason (hex : String)
  | linkedToContract (contractId : String)
  deriving DecidableEq, Repr

/-- A metadata value of a transition (`TransitionMetadata`). -/
inductive TransitionMetadata where
  | allowedInflation (n : Nat)
  | beforeBlock (n : Nat)
  deriving DecidableEq, Repr

/-- A transition (`RgbTransitionInfo`). -/
structure RgbTransitionInfo where
  type : TypeOfTransition
  opid : String
  inputs : List RgbInputInfo
  outputs : List RgbOutputInfo
  globals : List TransitionGlobal
  metadata : List TransitionMetadata
  deriving DecidableEq, Repr

/-- The transitions of one asset a witness commits (`RgbOperationInfo`). -/
structure RgbOperationInfo where
  assetId : String
  /-- Distinct transitions of the bundle's input map, inspected or not. -/
  committedTransitionCount : Nat
  /-- Entries of the bundle's input map. -/
  committedInputCount : Nat
  transitions : List RgbTransitionInfo
  deriving DecidableEq, Repr

/-- The witness commits transitions that are not inspected. -/
def RgbOperationInfo.hasConcealedTransitions (o : RgbOperationInfo) : Bool :=
  o.committedTransitionCount != o.transitions.length

/-- What a witness transaction commits (`RgbInspection`). -/
structure RgbInspection where
  txid : String
  closeMethod : DbcMethod
  commitmentHex : String
  operations : List RgbOperationInfo
  deriving DecidableEq, Repr

/-- Some inspected operation has concealed transitions. -/
def RgbInspection.hasConcealedTransitions (i : RgbInspection) : Bool :=
  i.operations.any (·.hasConcealedTransitions)

/-- A media file of an asset (`RgbMediaInfo`). -/
structure RgbMediaInfo where
  digest : String
  mime : String
  deriving DecidableEq, Repr

/-- An EVM contract (`RgbEvmContractInfo`). -/
structure RgbEvmContractInfo where
  chainId : Nat
  address : String
  deriving DecidableEq, Repr

/-- Where a bridge is deployed (`RgbBridgeLocationInfo`). -/
inductive RgbBridgeLocationInfo where
  | evm (c : RgbEvmContractInfo)
  deriving DecidableEq, Repr

/-- Where a reject list is published (`RgbRejectListInfo`). -/
inductive RgbRejectListInfo where
  | url (u : String)
  | evm (c : RgbEvmContractInfo)
  deriving DecidableEq, Repr

/-- The genesis of an asset (`RgbGenesisInfo`). -/
structure RgbGenesisInfo where
  /-- Prefix of the chain net (`bcrt` for regtest). -/
  chainNet : String
  timestamp : Int
  issuer : String
  name : String
  /-- None for CFA. -/
  ticker : Option String
  details : Option String
  precision : Nat
  /-- Supply issued by genesis: NIA, CFA and IFA. -/
  issuedSupply : Option Nat
  /-- IFA only. -/
  maxSupply : Option Nat
  linkedFromContract : Option String
  /-- BFA only. -/
  bridgeLocation : Option RgbBridgeLocationInfo
  rejectList : Option RgbRejectListInfo
  /-- Terms media, then the token media and attachments of a UDA. -/
  media : List RgbMediaInfo
  outputs : List RgbOutputInfo
  deriving DecidableEq, Repr

/-- A consignment (`ConsignmentInspection`). -/
structure ConsignmentInspection where
  consignmentId : String
  version : Nat
  isTransfer : Bool
  assetId : String
  assetSchema : AssetSchema
  genesis : RgbGenesisInfo
  /-- The selected witnesses, in consignment order. -/
  witnesses : List RgbInspection
  deriving DecidableEq, Repr

/-- The bundles of a consignment to inspect (`BundleFilter`). -/
inductive BundleFilter where
  | all
  /-- Bundles holding a terminal operation. -/
  | terminals
  /-- The bundle of the witness with this TXID. -/
  | witness (txid : String)
  deriving DecidableEq, Repr

/-! ## Inspection rules -/

/-- The assignment at `no` (`Assignment::from_typed_assigns`): fungible asset or inflation,
structured asset, declarative link or mint right; anything else is none. -/
def assignmentAt? {σ : Type} (t : AssignmentType) (ta : TypedAssigns σ) (no : Nat) :
    Option Assignment :=
  match ta with
  | .fungible l => (l[no]?).bind fun (_, v) =>
    if t == Schemas.osAsset then some (.fungible v.v)
    else if t == Schemas.osInflation then some (.inflationRight v.v) else none
  | .structured l => (l[no]?).bind fun _ => if t == Schemas.osAsset then some .nonFungible else none
  | .declarative l => (l[no]?).bind fun _ =>
    if t == Schemas.osLink then some .linkRight
    else if t == Schemas.osMint then some .mintRight else none

/-- The wallet kind of a transition type (`TypeOfTransition::try_from`). -/
def typeOfTransition? (t : TransitionType) : Option TypeOfTransition :=
  [TypeOfTransition.inflate, .transfer, .burn, .link, .transferInflation, .transferLink, .mint,
    .propagate].find? (·.transitionType == t)

/-- The error of an assignment rgb-lib cannot show: one the schema defines is "currently
unsupported", any other "unknown". -/
def unsupportedAssignment (context : String) (schema : Option AssetSchema)
    (ty : AssignmentType) : Error :=
  let inSchema := (schema.map (·.schema.ownedTypes.contains ty)).getD false
  let kind := if inSchema then "currently unsupported" else "unknown"
  .rgbInspection s!"{context}: {kind} assignment type: {ty}"

/-- `outputs_info`: every assignment, refused when rgb-lib cannot show it or, with a known
schema, the schema does not support it. A witness-output seal shows the witness TXID; a
concealed seal shows the recipient id of its blinded receive. -/
def outputsInfo (context : String) (schema : Option AssetSchema) (a : Assignments GraphSeal)
    (chainNet : ChainNet) (witness : Option Txid) (isTerminal : Option Bool) :
    Except Error (List RgbOutputInfo) := do
  let mut out : List RgbOutputInfo := []
  for (ty, ta) in a.toList do
    for no in List.range ta.len do
      let supported (x : Assignment) : Bool := (schema.map (·.supportsAssignment x)).getD true
      let some asg := (assignmentAt? ty ta no).filter supported
        | throw (unsupportedAssignment context schema ty)
      let some (bs, _) := ta.at? no | throw (unsupportedAssignment context schema ty)
      let info : RgbOutputInfo := match bs with
        | .revealed s =>
          let txid := match s.txptr with
            | .txid t => some t
            | .witnessTx => witness
          { txid := txid.map toString, vout := some s.vout.toNat, blinding := some s.blinding
            assignment := asg, isConcealed := false, recipientId := none, isOurs := none
            isTerminal }
        | .concealed secret =>
          { txid := none, vout := none, blinding := none, assignment := asg, isConcealed := true
            recipientId := some s!"{chainNet.prefix_}:{secret}", isOurs := none, isTerminal }
      out := out ++ [info]
  return out

/-- A global value of a transition (`transition_info`): issued supply, burned amounts, burn
reason and link target; any other type is refused. -/
def transitionGlobal (ctx : String) (t : GlobalStateType) (v : RevealedData) :
    Except Error TransitionGlobal :=
  let invalid (name : String) : Except Error TransitionGlobal :=
    .error (.rgbInspection s!"{ctx}: invalid {name} global: {reprStr v.v.semId} value")
  if t == Schemas.gsIssuedSupply then
    match v.v with | .amount a => .ok (.issuedSupply a.toNat) | _ => invalid "issuedSupply"
  else if t == Schemas.gsBurnedAsset then
    match v.v with | .amount a => .ok (.burnedAsset a.toNat) | _ => invalid "burnedAsset"
  else if t == Schemas.gsBurnedInflation then
    match v.v with | .amount a => .ok (.burnedInflation a.toNat) | _ => invalid "burnedInflation"
  else if t == Schemas.gsBurnReason then
    match v.v with
    | .burnReason r => if r.valid then .ok (.burnReason (Hex.ofBytes r.bytes)) else
        invalid "burnReason"
    | _ => invalid "burnReason"
  else if t == Schemas.gsLinkedToContract then
    match v.v with
    | .contractId d => .ok (.linkedToContract (toString (ContractId.mk d)))
    | _ => invalid "linkedToContract"
  else .error (.rgbInspection s!"{ctx}: unknown global state type: {t}")

/-- A metadata value of a transition: allowed inflation and before block; any other type is
refused. -/
def transitionMetadata (ctx : String) (t : MetaType) (v : MetaValue) :
    Except Error TransitionMetadata :=
  let invalid (name : String) : Except Error TransitionMetadata :=
    .error (.rgbInspection s!"{ctx}: invalid {name} metadata: {reprStr v.v.semId} value")
  if t == Schemas.msAllowedInflation then
    match v.v with | .amount a => .ok (.allowedInflation a.toNat) | _ => invalid "allowedInflation"
  else if t == Schemas.msBeforeBlock then
    match v.v with | .blockNumber b => .ok (.beforeBlock b.v.toNat) | _ => invalid "beforeBlock"
  else .error (.rgbInspection s!"{ctx}: unknown metadata type: {t}")

/-- `transition_info`: type, outputs, globals and metadata of a transition. -/
def transitionInfo (cid : ContractId) (schema : Option AssetSchema) (t : Transition)
    (chainNet : ChainNet) (witness : Txid) (inputs : List RgbInputInfo)
    (isTerminal : Option Bool) : Except Error RgbTransitionInfo := do
  let ctx := s!"bundle for contract {cid}"
  let some ty := typeOfTransition? t.transitionType
    | throw (.rgbInspection s!"{ctx}: unknown transition type: {t.transitionType}")
  let outputs ← outputsInfo ctx schema t.assignments chainNet (some witness) isTerminal
  let mut globals : List TransitionGlobal := []
  for (gt, vals) in t.globals.toList do
    for v in vals do
      globals := globals ++ [← transitionGlobal ctx gt v]
  let mut metadata : List TransitionMetadata := []
  for (mt, v) in t.metadata.toList do
    metadata := metadata ++ [← transitionMetadata ctx mt v]
  return { type := ty, opid := toString t.id, inputs, outputs, globals, metadata }

/-- `bundle_output`: an opout another transition of the bundle assigns to a revealed seal on
a known transaction. -/
def bundleOutput (b : TransitionBundle) (o : Opout) : Option (Outpoint × Assignment) := do
  let t ← b.transition? o.op
  let ta ← t.assignments.find? o.ty
  let (bs, _) ← ta.at? o.no.toNat
  let s ← bs.revealed?
  let op ← s.outpoint?
  let a ← assignmentAt? o.ty ta o.no.toNat
  return (op, a)

/-- `bundle_info`: an input the bundle assigns must resolve within it, whether or not
`resolveInputs` asks every input to resolve. -/
def bundleInfo (cid : ContractId) (schema : Option AssetSchema) (chainNet : ChainNet)
    (bundle : TransitionBundle) (tx : Tx) (checkCommitments resolveInputs : Bool)
    (resolveInput : Opout → Option (Outpoint × Assignment))
    (isTerminal : OpId → Option Bool) : Except Error RgbOperationInfo := do
  let ctx := s!"bundle for contract {cid}"
  let opids := bundle.knownTransitions.map (·.opid)
  for (o, i) in opids.zipIdx do
    if (opids.take i).contains o then
      throw (.rgbInspection s!"{ctx}: transition {o} is listed twice")
  let mut transitions : List RgbTransitionInfo := []
  for kt in bundle.knownTransitions do
    let t := kt.transition
    if t.contractId != cid then
      throw (.rgbInspection s!"{ctx}: transition {kt.opid} is of contract {t.contractId}")
    let committed := !checkCommitments || (t.id == kt.opid && !t.inputs.isEmpty &&
      t.inputs.all fun i => bundle.inputMap.find? i == some kt.opid)
    if !committed then throw (.rgbInspection s!"{ctx}: transition {kt.opid} is not committed")
    let mut inputs : List RgbInputInfo := []
    for i in t.inputs do
      let inBundle := opids.contains i.op
      let resolved := match bundleOutput bundle i with
        | some r => some r
        | none => resolveInput i
      let (vin, asg) ← match resolved with
        | some (o, a) =>
          match tx.inputs.findIdx? (·.prevout == o) with
          | some v => pure (some v, some a)
          | none => throw (.rgbInspection s!"{ctx}: input {i} not spent by witness {tx.txid}")
        | none =>
          if inBundle then
            throw (.rgbInspection (s!"{ctx}: input {i} isn't assigned by the bundle to an " ++
              "outpoint the witness spends"))
          else if resolveInputs then throw (.rgbInspection s!"{ctx}: unknown input {i}")
          else pure (none, none)
      let some ty := TypeOfAssignment.of? i.ty
        | throw (.rgbInspection s!"{ctx}: unknown assignment type: {i.ty}")
      inputs := inputs ++ [⟨⟨toString i.op, ty, i.no.toNat⟩, vin, asg⟩]
    transitions := transitions ++
      [← transitionInfo cid schema t chainNet tx.txid inputs (isTerminal kt.opid)]
  return { assetId := toString cid, committedTransitionCount := bundle.inputMapOpids.size
           committedInputCount := bundle.inputMap.size, transitions }

/-- The witness carries the commitment (`verify_witness_commitment`). -/
def verifyWitnessCommitment (proof : DbcProof) (commitment : Digest) (tx : Tx) :
    Except Error Unit :=
  match proof.verify commitment tx with
  | .ok () => .ok ()
  | .error e =>
    .error (.rgbInspection s!"witness {tx.txid} doesn't commit to {commitment}: {reprStr e}")

/-- Decode the first value of a genesis global with `f`: none when absent, refused when it
does not decode. -/
def readGlobal {α : Type} (ctx : String) (g : Genesis) (t : GlobalStateType)
    (f : StrictValue → Option α) : Except Error (Option α) :=
  match firstGlobal? g t with
  | none => .ok none
  | some v =>
    match if v.wellFormed then f v else none with
    | some a => .ok (some a)
    | none => .error (.rgbInspection s!"{ctx}: invalid {t} global: {reprStr v.semId} value")

/-- A genesis global the schema requires. -/
def requireGlobal {α : Type} (ctx : String) (g : Genesis) (t : GlobalStateType)
    (f : StrictValue → Option α) : Except Error α := do
  match ← readGlobal ctx g t f with
  | some a => pure a
  | none => throw (.rgbInspection s!"{ctx}: missing {t} global")

/-- A media file as inspection shows it: the digest and `type/subtype` (`*` when absent). -/
def mediaInfo (a : Attachment) : RgbMediaInfo :=
  ⟨a.digest, a.ty.ty ++ "/" ++ a.ty.subtype.getD "*"⟩

/-- An EVM contract as inspection shows it. -/
def evmContractInfo (c : EvmContract) : RgbEvmContractInfo :=
  ⟨c.chainId.toNat, addressText c.address⟩

/-- `genesis_info`: the first value of each global the schema defines; a required one that is
missing, or any that does not decode, is refused. -/
def genesisInfo (cid : ContractId) (schema : AssetSchema) (g : Genesis) :
    Except Error RgbGenesisInfo := do
  let ctx := s!"genesis of contract {cid}"
  let (name, ticker, details, precision) ← match schema with
    | .cfa => do
      let name ← requireGlobal ctx g Schemas.gsName (fun | .name n => some n | _ => none)
      let details ← readGlobal ctx g Schemas.gsDetails (fun | .details d => some d | _ => none)
      let precision ← requireGlobal ctx g Schemas.gsPrecision
        (fun | .precision p => some p | _ => none)
      pure (name.s, none, details.map (·.s), precision)
    | .bfa => do
      let ticker ← requireGlobal ctx g Schemas.gsTicker
        (fun | .unicodeTicker t => some t | _ => none)
      let name ← requireGlobal ctx g Schemas.gsName (fun | .name n => some n | _ => none)
      let details ← readGlobal ctx g Schemas.gsDetails (fun | .details d => some d | _ => none)
      let precision ← requireGlobal ctx g Schemas.gsPrecision
        (fun | .precision p => some p | _ => none)
      pure (name.s, some ticker.s, details.map (·.s), precision)
    | .nia | .uda | .ifa => do
      let spec ← requireGlobal ctx g Schemas.gsNominal (fun | .assetSpec s => some s | _ => none)
      pure (spec.name.s, some spec.ticker.s, spec.details.map (·.s), spec.precision)
  let amount : StrictValue → Option UInt64 := fun | .amount a => some a | _ => none
  let issuedSupply ← match schema with
    | .nia | .cfa | .ifa => some <$> requireGlobal ctx g Schemas.gsIssuedSupply amount
    | .uda | .bfa => pure none
  let maxSupply ← match schema with
    | .ifa => some <$> requireGlobal ctx g Schemas.gsMaxSupply amount
    | _ => pure none
  let linkedFrom ← match schema with
    | .ifa | .bfa =>
      readGlobal ctx g Schemas.gsLinkedFromContract (fun | .contractId d => some d | _ => none)
    | _ => pure none
  let bridge ← match schema with
    | .bfa =>
      match bridgeLocation g with
      | .ok (.evm c) => pure (some (RgbBridgeLocationInfo.evm (evmContractInfo c)))
      | .error e =>
        throw (.rgbInspection s!"{ctx}: invalid {Schemas.gsBridgeLocation} global: {e}")
    | _ => pure none
  let rejectList ← match genesisRejectListSource schema g with
    | .ok none => pure none
    | .ok (some (.url u)) => pure (some (RgbRejectListInfo.url u))
    | .ok (some (.evm c)) => pure (some (RgbRejectListInfo.evm (evmContractInfo c)))
    | .error e => throw (.rgbInspection s!"{ctx}: invalid reject list global: {e}")
  let terms ← requireGlobal ctx g Schemas.gsTerms (fun | .contractTerms t => some t | _ => none)
  let mut media := terms.media.toList.map mediaInfo
  if schema == .uda then
    let token ← requireGlobal ctx g Schemas.gsTokens (fun | .tokenData t => some t | _ => none)
    let attachments := token.attachments.mergeSort fun a b => a.1 ≤ b.1
    media := media ++ token.media.toList.map mediaInfo ++ attachments.map (mediaInfo ·.2)
  let outputs ← outputsInfo ctx (some schema) (Operation.genesis g).assignments g.chainNet none
    (some false)
  return { chainNet := g.chainNet.prefix_, timestamp := g.timestamp, issuer := g.issuer.s, name
           ticker, details, precision := precision.decimals
           issuedSupply := issuedSupply.map (·.toNat), maxSupply := maxSupply.map (·.toNat)
           linkedFromContract := linkedFrom.map fun d => toString (ContractId.mk d)
           bridgeLocation := bridge, rejectList, media, outputs }

/-- `consignment_inspection`: inputs resolve from genesis or from a transition listed under its
own id; a transition in the bundles of two witnesses is refused. -/
def consignmentInspection (c : Consignment) (selected : Txid → Bool → Bool) :
    Except Error ConsignmentInspection := do
  let cid := c.contractId
  let some schema := AssetSchema.ofSchemaId? c.schemaId
    | throw (.unknownRgbSchema (toString c.schemaId))
  let genesis ← genesisInfo cid schema c.genesis
  let mut index : List (OpId × Transition × Txid) := []
  for wb in c.bundles do
    for kt in wb.bundle.knownTransitions do
      if kt.transition.id == kt.opid then
        match index.find? (·.1 == kt.opid) with
        | some (_, _, w) =>
          if w != wb.witnessId then
            throw (.rgbInspection
              s!"transition {kt.opid} in the bundles of witnesses {w} and {wb.witnessId}")
        | none => index := index ++ [(kt.opid, kt.transition, wb.witnessId)]
  let resolveInput (o : Opout) : Option (Outpoint × Assignment) :=
    if o.op == c.genesis.id then do
      let ta ← c.genesis.assignments.find? o.ty
      let (bs, _) ← ta.at? o.no.toNat
      let s ← bs.revealed?
      let a ← assignmentAt? o.ty ta o.no.toNat
      return (s.outpoint, a)
    else do
      let (_, t, w) ← index.find? (·.1 == o.op)
      let ta ← t.assignments.find? o.ty
      let (bs, _) ← ta.at? o.no.toNat
      let s ← bs.revealed?
      let a ← assignmentAt? o.ty ta o.no.toNat
      return (s.outpointOr w, a)
  let terminal := c.terminalOps
  let mut witnesses : List RgbInspection := []
  for wb in c.bundles do
    let bid := wb.bundle.bundleId
    let txid := wb.witnessId
    let hasTerminals := wb.bundle.knownTransitions.any fun kt => terminal.contains kt.opid
    if selected txid hasTerminals then
      let commitment ← match wb.anchor.mpcProof.convolve cid bid with
        | .ok cm => pure cm
        | .error e =>
          throw (.rgbInspection s!"bundle {bid} not committed by witness {txid}: {reprStr e}")
      verifyWitnessCommitment wb.anchor.dbcProof commitment wb.tx
      let op ← bundleInfo cid (some schema) c.genesis.chainNet wb.bundle wb.tx true true
        resolveInput fun o => some (terminal.contains o)
      witnesses := witnesses ++ [{ txid := toString txid, closeMethod := wb.anchor.dbcProof.method
                                   commitmentHex := toString commitment, operations := [op] }]
  return { consignmentId := toString c.consignmentId, version := 1, isTransfer := c.transfer
           assetId := toString cid, assetSchema := schema, genesis, witnesses }

/-- `inspect_consignment`: the path, the filter's TXID, then any consignment file (validated
ones included, without trusting them); a TXID filter that selects nothing is refused. -/
def inspectConsignment (path : String) (file : ConsignmentFile) (filter : BundleFilter) :
    Except Error ConsignmentInspection := do
  match file with
  | .missing => throw (.invalidFilePath path)
  | _ => pure ()
  let witness ← match filter with
    | .witness t =>
      match idText? t with
      | some w => pure (some w)
      | none => throw .invalidTxid
    | _ => pure none
  let selected (txid : Txid) (hasTerminals : Bool) : Bool := match filter with
    | .all => true
    | .terminals => hasTerminals
    | .witness _ => witness == some (toString txid)
  let c ← match file with
    | .transfer c | .contract c | .validated _ c => pure c
    | _ => throw .invalidConsignment
  let r ← consignmentInspection c selected
  if let some w := witness then
    if r.witnesses.isEmpty then throw (.rgbInspection s!"witness {w} not found in the consignment")
  return r

/-- A fascia file as `fascia_from_file` reads it. -/
inductive FasciaFile where
  /-- It cannot be opened. -/
  | missing
  /-- Not a regular file. -/
  | notRegular
  /-- A file of `size` bytes: the fascia it starts with, if any, and whether bytes follow it. -/
  | file (size : Nat) (fascia : Option Fascia) (trailing : Bool)
  deriving DecidableEq, Repr

/-- `fascia_from_file`: a larger file than `maxSize` is refused before decoding; the file must
be exactly one fascia. -/
def fasciaFromFile (path : String) (f : FasciaFile) (maxSize : Nat) : Except Error Fascia :=
  match f with
  | .missing | .notRegular => .error (.invalidFilePath path)
  | .file size fascia trailing =>
    if size > maxSize then .error (.fileTooLarge path maxSize)
    else match fascia with
      | some fa => if trailing then .error (.invalidFilePath path) else .ok fa
      | none => .error (.invalidFilePath path)

/-- `fascia_inspection`: the MPC commitment rebuilt from the fascia's bundles alone must be the
one the transaction carries, so the transaction commits to these bundles only. -/
def fasciaInspection (tx : Tx) (f : Fascia) (entropy : Option UInt64) (maxBundles : Nat)
    (chainNet : ChainNet) : Except Error RgbInspection := do
  if f.witnessId != tx.txid then
    throw (.rgbInspection s!"fascia witness ID {f.witnessId} does not match PSBT TXID {tx.txid}")
  let n := f.bundles.size
  if n > maxBundles then
    throw (.rgbInspection s!"fascia bundle count {n} exceeds the maximum of {maxBundles}")
  let mut ops : List RgbOperationInfo := []
  for (cid, b) in f.bundles.toList do
    ops := ops ++ [← bundleInfo cid none chainNet b tx true false (fun _ => none) (fun _ => none)]
  let messages := OrdMap.ofList (f.bundles.toList.map fun (cid, b) => (cid, b.bundleId))
  let carried : Option UInt64 := some f.sealWitness.mpcTree.entropy
  let e ← match entropy, carried with
    | some g, some c =>
      if g != c then
        throw (.rgbInspection (s!"the MPC commitment of the fascia was built with entropy {c}, " ++
          s!"not the given {g}"))
      else pure g
    | some g, none => pure g
    | none, some c => pure c
    | none, none =>
      throw (.rgbInspection ("the MPC commitment of the fascia doesn't carry the entropy it " ++
        "was built with, which then has to be given"))
  let tree ← match Mpc.MerkleTree.tryCommit messages e with
    | .ok t => pure t
    | .error err =>
      throw (.rgbInspection
        s!"cannot rebuild the MPC commitment of the fascia bundles: {reprStr err}")
  verifyWitnessCommitment f.sealWitness.dbcProof tree.commitment tx
  return { txid := toString tx.txid, closeMethod := f.sealWitness.dbcProof.method
           commitmentHex := toString tree.commitment, operations := ops }

/-- `inspect_fascia`; the PSBT is its unsigned transaction. Without a wallet an input outside
the bundle shows its opout only, and no schema checks the assignment types. -/
def inspectFascia (psbt : Tx) (path : String) (file : FasciaFile) (entropy : Option UInt64)
    (maxFasciaSize maxBundles : Nat) (network : BitcoinNetwork) : Except Error RgbInspection := do
  let f ← fasciaFromFile path file maxFasciaSize
  fasciaInspection psbt f entropy maxBundles network.chainNet

/-! ## SPV proofs -/

/-- A witness the indexer has no SPV proof for (`WitnessWithoutProof`). -/
structure WitnessWithoutProof where
  txid : String
  details : String
  deriving DecidableEq, Repr

/-- Report of `fill_spv_proofs` (`SpvProofFill`). -/
structure SpvProofFill where
  /-- Sorted by TXID. -/
  withoutProof : List WitnessWithoutProof
  /-- The file is rewritten only when a proof was added. -/
  rewritten : Bool
  deriving DecidableEq, Repr

/-- `fill_spv_proofs`, with the rewritten consignment if any: a failure about one witness is
reported, any other fails the call; proofs a bundle carries are kept, even stale ones. -/
def fillSpvProofs (path : String) (file : ConsignmentFile) (indexer : Indexer) :
    Except Error (SpvProofFill × Option Consignment) := do
  match file with
  | .missing => throw (.invalidFilePath path)
  | _ => pure ()
  let c ← match file with
    | .transfer c => pure c
    | _ => throw .invalidConsignment
  let network ← BitcoinNetwork.ofChainNet c.genesis.chainNet
  match indexer.resolver.checkChainNet network.chainNet with
  | .error e => throw (.invalidIndexer (reprStr e))
  | .ok () => pure ()
  let missing := ((c.bundles.filter (·.spvProof.isNone)).map (·.witnessId)).eraseDups.mergeSort
    fun a b => compare a b != .gt
  let mut c := c
  let mut without : List WitnessWithoutProof := []
  let mut rewritten := false
  for w in missing do
    match indexer.resolveSpvProof w with
    | .ok p =>
      c := { c with bundles := c.bundles.map fun wb =>
        if wb.witnessId == w && wb.spvProof.isNone then { wb with spvProof := some p } else wb }
      rewritten := true
    | .error e =>
      match e with
      | .resolverIssue (some t) d =>
        if t == w then without := without ++ [⟨toString w, d⟩]
        else throw (.indexer (reprStr e))
      | _ => throw (.indexer (reprStr e))
  let report : SpvProofFill :=
    { withoutProof := without.mergeSort fun a b => compare a.txid b.txid != .gt, rewritten }
  return (report, if rewritten then some c else none)

end Rgb.Lib.NoWallet
