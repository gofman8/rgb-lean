import Rgb.Lib.Backup

/-!
# rgb-lib multisig wallets

Multisig keys and descriptors (`MultisigKeys`), and how the cosigners of a group
coordinate through the multisig hub (`wallet/multisig.rs`, `api/multisig_hub.rs`).

Every cosigner runs its own wallet with the same keys. A cosigner initiates an
operation by posting it to the hub with its unsigned PSBT; the cosigners answer with
an ACK (the PSBT signed) or a NACK. The hub approves the operation when the ACKs
reach the threshold and discards it when they can no longer reach it. Each wallet
processes the hub's operations one at a time, in index order (`sync_with_hub`): an
approved operation is executed (its PSBTs combined, finalized and broadcast), a
discarded one skipped, and either is then marked processed on the hub. Issuances and
receives are approved when they are posted. A watch-only user reads the hub and
follows the cosigners' decisions but cannot change anything.

The hub server is not part of rgb-lib, so its rules are UNCERTAIN from rgb-lib's
side: the model takes them from the rgb-multisig-hub server source, and the rgb-lib
tests agree with them. Each hub rule says so. Wallet calls run in `WalletM`: they
change the wallet and the hub, and changes made before an error stay (a hub call
that succeeded is not undone).
-/

namespace Rgb.Lib

open Bip32

/-! ## Cosigners and keys -/

/-- Most cosigners of a group: counts and thresholds are `u8`. -/
def maxCosigners : Nat := 255

/-- Internal key of the multisig descriptors on mainnet: the BIP-341 H point with a
zero chain code (`NUMS_XPUB_MAINNET`). -/
def numsXpubMainnet : String :=
  "xpub661MyMwAqRbcEYS8w7XLSVeEsBXy79zSzH1J8vCdxAZningWLdN3zgtU6QgnecKFpJFPpdzxKrwo" ++
  "aZoV44qAJewsc4kX9vGaCaBExuvJH57"

/-- The same key on the other networks (`NUMS_TPUB_TESTNET`). -/
def numsTpubTestnet : String :=
  "tpubD6NzVbkrYhZ4WLczPJWReQycCJdd6YVWXubbVUFnJ5KgU5MDQrD998ZJLSmaB7GVcCnJSDWprxmr" ++
  "GkJ6SvgQC6QAffVpqSvonXmeizXcrkN"

/-- A member of a multisig group (`Cosigner`). -/
structure Cosigner where
  accountXpubVanilla : String
  accountXpubColored : String
  /-- Vanilla keychain index; `none` counts as 0. -/
  vanillaKeychain : Option Nat := none
  masterFingerprint : String
  deriving DecidableEq, Repr, Inhabited

namespace Cosigner

/-- The cosigner of a set of keys. -/
def ofKeys (k : Keys) (vanillaKeychain : Option Nat := none) : Cosigner :=
  { accountXpubVanilla := k.accountXpubVanilla, accountXpubColored := k.accountXpubColored
    vanillaKeychain, masterFingerprint := k.masterFingerprint }

/-- `fingerprint:vanilla xpub:colored xpub:keychain` (`Display`). -/
def render (c : Cosigner) : String :=
  ":".intercalate [c.masterFingerprint, c.accountXpubVanilla, c.accountXpubColored,
    s!"{c.vanillaKeychain.getD keychainBtc}"]

/-- A `u8` in decimal, with an optional leading `+` (`u8::from_str`). -/
def parseU8? (s : String) : Option Nat :=
  let ds := match s.toList with
    | '+' :: rest => rest
    | cs => cs
  if !ds.isEmpty && ds.all Char.isDigit then
    let v := ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    if v ≤ 255 then some v else none
  else none

/-- Parse a cosigner (`FromStr`); the keychain becomes explicit. Exactly four parts are
needed, though the error text says three or four. -/
def parse (s : String) : Result Cosigner := do
  let parts := s.splitOn ":"
  let [fp, xv, xc, kc] := parts
    | throw (.invalidCosigner s!"expected 3 or 4 colon-separated parts, got {parts.length}")
  if (parseFingerprint? fp).isNone then
    throw (.invalidCosigner s!"invalid master_fingerprint '{fp}'")
  if (Xpub.parse? xv).isNone then throw (.invalidCosigner s!"invalid vanilla xpub '{xv}'")
  if (Xpub.parse? xc).isNone then throw (.invalidCosigner s!"invalid colored xpub '{xc}'")
  let some k := parseU8? kc | throw (.invalidCosigner s!"invalid vanilla_keychain value '{kc}'")
  return { accountXpubVanilla := xv, accountXpubColored := xc, vanillaKeychain := some k
           masterFingerprint := fp }

end Cosigner

/-- Keys of a multisig wallet (`MultisigKeys`): the cosigners and the thresholds of the
colored and the vanilla side. -/
structure MultisigKeys where
  cosigners : List Cosigner
  thresholdColored : Nat
  thresholdVanilla : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A cosigner key of a multisig descriptor: `[fp/86'/coin'/0']xpub/keychain/*`. -/
def multisigKey (fp : String) (coin : Nat) (xpub : String) (keychain : Nat) : String :=
  s!"[{fp}/{purposeMultisig}'/{coin}'/{account}']{xpub}/{keychain}/*"

/-- `tr(nums/0/*,multi_a(threshold,k1,...,kn))`. -/
def trMultiA (nums : String) (threshold : Nat) (keys : List String) : String :=
  s!"tr({nums}/0/*,multi_a({threshold},{",".intercalate keys}))"

/-- Descriptors of multisig keys (`MultisigKeys::build_descriptors`). Every key path claims
purpose 86, whatever witness version made the xpubs, and repeated keys are not refused;
the keys of each side are sorted, so every cosigner builds the same descriptors. -/
def MultisigKeys.buildDescriptors (k : MultisigKeys) (network : BitcoinNetwork) :
    Result WalletDescriptors := do
  if k.cosigners.isEmpty then throw .noCosignersSupplied
  let n := k.cosigners.length
  if n > maxCosigners then throw .tooManyCosigners
  for t in [k.thresholdColored, k.thresholdVanilla] do
    if t == 0 || t > n then throw (.invalidMultisigThreshold t n)
  let keyFor (c : Cosigner) (colored : Bool) : Result String := do
    if (parseFingerprint? c.masterFingerprint).isNone then
      throw (.invalidCosigner s!"invalid master_fingerprint '{c.masterFingerprint}'")
    let side := if colored then "colored" else "vanilla"
    let xs := if colored then c.accountXpubColored else c.accountXpubVanilla
    let some x := Xpub.parse? xs | throw (.invalidCosigner s!"invalid {side} xpub '{xs}'")
    if x.kind != .ofNetwork network then
      throw (.invalidCosigner s!"{side} xpub '{xs}' is for the wrong network")
    let keychain := if colored then keychainRgb else c.vanillaKeychain.getD keychainBtc
    return multisigKey c.masterFingerprint (coinType network colored) x.toString keychain
  let keys ← k.cosigners.mapM fun c => do
    let kc ← keyFor c true
    let kv ← keyFor c false
    return (kc, kv)
  let sorted (l : List String) := l.mergeSort fun a b => decide (a ≤ b)
  let nums := if network == .mainnet then numsXpubMainnet else numsTpubTestnet
  return { colored := trMultiA nums k.thresholdColored (sorted (keys.map (·.1)))
           vanilla := trMultiA nums k.thresholdVanilla (sorted (keys.map (·.2))) }

/-- Directory name of a multisig wallet: the first 8 hex digits of SHA-256 of
`colored|vanilla` (a symbolic digest here). -/
def WalletDescriptors.multisigDirName (d : WalletDescriptors) : String :=
  (Digest.of "sha256" [d.colored ++ "|" ++ d.vanilla]).short

/-- Checks of `MultisigWallet::new` before the shared wallet setup; returns the
descriptors and the wallet directory name. Addresses come from the hub, so no reuse. -/
def MultisigKeys.checkNewWallet (k : MultisigKeys) (data : WalletData) :
    Result (WalletDescriptors × String) := do
  if data.addressReuseVanilla || data.addressReuseColoredAuto then
    throw (.unsupportedAddressReuse "multisig wallets don't support it")
  let d ← k.buildDescriptors data.bitcoinNetwork
  return (d, d.multisigDirName)

namespace Multisig

/-! ## Operations and files -/

/-- Operation types (`OperationType`, wire values 1..8). -/
inductive OperationType where
  | createUtxos
  | issuance
  | sendRgb
  | sendBtc
  | inflation
  | blindReceive
  | witnessReceive
  | burn
  deriving DecidableEq, Repr, Inhabited

namespace OperationType

/-- Wire value. -/
def code : OperationType → Nat
  | createUtxos => 1 | issuance => 2 | sendRgb => 3 | sendBtc => 4 | inflation => 5
  | blindReceive => 6 | witnessReceive => 7 | burn => 8

/-- Issuances and receives are approved when posted; the other types need votes. -/
def autoApproved : OperationType → Bool
  | issuance | blindReceive | witnessReceive => true
  | _ => false

/-- Types posted with the operation seed (`OPERATION_TYPES_REQUIRING_SEED`). -/
def requiresSeed : OperationType → Bool
  | sendRgb | blindReceive | witnessReceive => true
  | _ => false

/-- RGB operations, whose data and fascia travel with them. -/
def isRgb : OperationType → Bool
  | sendRgb | inflation | burn => true
  | _ => false

/-- Hub rule: bitcoin-only operations need the vanilla threshold, RGB ones the colored
threshold; auto-approved ones have none. -/
def threshold? (t : OperationType) (colored vanilla : Nat) : Option Nat :=
  match t with
  | createUtxos | sendBtc => some vanilla
  | sendRgb | inflation | burn => some colored
  | issuance | blindReceive | witnessReceive => none

/-- Field of the operation data holding the operation key (`operation_key_name`). -/
def keyName? : OperationType → Option String
  | sendRgb => some "operation_secret_key"
  | blindReceive | witnessReceive => some "seed"
  | _ => none

end OperationType

/-- Hub status of an operation (`OperationStatus`). -/
inductive OperationStatus where
  | pending
  | approved
  | discarded
  deriving DecidableEq, Repr, Inhabited

/-- Kinds of operation files (`FileType`). -/
inductive FileType where
  | consignment
  | media
  | operationData
  | operationPsbt
  | responsePsbt
  | fascia
  deriving DecidableEq, Repr, Inhabited

/-- Multipart field a file is posted in (`FileType::field_name`). -/
def FileType.fieldName : FileType → String
  | .operationPsbt | .responsePsbt => "file_psbt"
  | .consignment => "file_consignment"
  | .media => "file_media"
  | .operationData => "file_operation_data"
  | .fascia => "file_fascia"

/-- A PSBT (symbolic): the txid of its unsigned transaction and the keys that signed. -/
structure Psbt where
  txid : String
  signers : List String := []
  deriving DecidableEq, Repr, Inhabited

namespace Psbt

/-- PSBT text: `psbt:<txid>`, then `:<key>` per signature. -/
def render (p : Psbt) : String := ":".intercalate ("psbt" :: p.txid :: p.signers)

/-- Parse PSBT text (`Psbt::from_str`). -/
def parse? (s : String) : Option Psbt :=
  match s.splitOn ":" with
  | "psbt" :: txid :: signers => if txid.isEmpty then none else some { txid, signers }
  | _ => none

/-- Add the signature of a key. -/
def sign (p : Psbt) (key : String) : Psbt := { p with signers := p.signers ++ [key] }

/-- `Psbt::combine`: PSBTs of one transaction, with their signatures merged. -/
def combine? (a b : Psbt) : Option Psbt :=
  if a.txid == b.txid then some { a with signers := (a.signers ++ b.signers).eraseDups } else none

end Psbt

/-- `invalidPsbt` text of a string that is not a PSBT (`PsbtParseError`). -/
def psbtParseError : String := "error in PSBT base64 encoding"

/-- Operation data of a send, inflation or burn (`InfoBatchTransfer`): what the checks
read. -/
structure BatchTransferData where
  /-- Main transition of each asset transfer. -/
  transitions : List TypeOfTransition
  minConfirmations : Nat := 1
  entropy : Nat := 0
  donation : Bool := false
  burnReason : Option String := none
  /-- Operation seed of a send; legacy operation data lacks it. -/
  operationSecretKey : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- Every transfer has main transition `t`, and there is one (`is_operation`). -/
def BatchTransferData.isOperation (d : BatchTransferData) (t : TypeOfTransition) : Bool :=
  !d.transitions.isEmpty && d.transitions.all (· == t)

/-- Operation data of a receive (`ReceiveMetadata`). -/
structure ReceiveMetadata where
  invoice : String
  /-- Recipient ID of the invoice. -/
  recipientId : String
  minConfirmations : Nat := 1
  expirationTimestamp : Nat
  /-- The blinded UTXO of a blind receive. -/
  secretSeal : Option String := none
  /-- Operation seed (hex); legacy operation data lacks it. -/
  seed : Option String
  deriving DecidableEq, Repr, Inhabited

/-- Content of a hub file (symbolic). -/
inductive FileContent where
  | psbt (p : Psbt)
  | batchTransfer (d : BatchTransferData)
  | receive (m : ReceiveMetadata)
  | fascia (txid : String)
  /-- An issued contract with the digests of its attachments. -/
  | contract (assetId : String) (attachments : List String)
  | media (digest : String)
  /-- Bytes that are none of the above. -/
  | invalid
  deriving DecidableEq, Repr, Inhabited

/-- File id: hex SHA-256 of the content (a symbolic digest here). -/
def FileContent.fileId (c : FileContent) : String := (Digest.of "sha256" [reprStr c]).short

/-- Whether JSON operation data holds the key, not null; `none` for data that is not
JSON. -/
def FileContent.hasKey? (c : FileContent) (key : String) : Option Bool :=
  match c with
  | .batchTransfer d => some (key == "operation_secret_key" && d.operationSecretKey.isSome)
  | .receive m => some (key == "seed" && m.seed.isSome)
  | _ => none

/-- A file of an operation as the hub lists it (`FileMetadata`), with its content. -/
structure FileMetadata where
  fileId : String
  fileType : FileType
  postedBy : String
  content : FileContent
  deriving DecidableEq, Repr, Inhabited

/-- A file of posted content. -/
def FileMetadata.ofContent (t : FileType) (postedBy : String) (c : FileContent) : FileMetadata :=
  { fileId := c.fileId, fileType := t, postedBy, content := c }

/-! ## The hub -/

/-- Role of a hub user (`UserRole`). -/
inductive UserRole where
  | cosigner
  | watchOnly
  deriving DecidableEq, Repr, Inhabited

/-- Who calls the hub, as the token says: a cosigner by its colored account xpub, or a
watch-only user. -/
inductive HubUser where
  | cosigner (xpub : String)
  | watchOnly
  deriving DecidableEq, Repr, Inhabited

/-- Error body of a failed hub call (`APIErrorBody`): the message and the error name. -/
structure HubError where
  error : String
  name : String
  deriving DecidableEq, Repr, Inhabited

namespace HubError

/-- `CannotPostNewOperation`. -/
def cannotPost (d : String) : HubError :=
  ⟨s!"Cannot post new operation: {d}", "CannotPostNewOperation"⟩
/-- `CannotRespondToOperation`. -/
def cannotRespond (d : String) : HubError :=
  ⟨s!"Cannot respond to operation: {d}", "CannotRespondToOperation"⟩
/-- `CannotMarkOperationProcessed`. -/
def cannotMark (d : String) : HubError :=
  ⟨s!"Cannot mark operation as processed: {d}", "CannotMarkOperationProcessed"⟩
/-- `OperationNotFound`. -/
def operationNotFound : HubError := ⟨"Operation not found", "OperationNotFound"⟩
/-- `TransferStatusMismatch`. -/
def transferStatusMismatch : HubError :=
  ⟨"Transfer status already set to a different value", "TransferStatusMismatch"⟩
/-- `InvalidCount`. -/
def invalidCount : HubError := ⟨"Invalid count: must be greater than 0", "InvalidCount"⟩
/-- `InvalidRequest`. -/
def invalidRequest (d : String) : HubError := ⟨s!"Invalid request: {d}", "InvalidRequest"⟩
/-- A watch-only user on a cosigner route (the authentication layer). -/
def forbiddenRoute : HubError := ⟨"You don't have access to this resource", "Forbidden"⟩
/-- A watch-only user setting a transfer status. -/
def forbidden : HubError := ⟨"Forbidden", "Forbidden"⟩
/-- A token the hub does not accept. -/
def unauthorized : HubError := ⟨"Missing or invalid credentials", "Unauthorized"⟩

/-- The rgb-lib error of a hub error (`map_hub_error`). -/
def toError (e : HubError) : Error :=
  match e.name with
  | "CannotPostNewOperation" => .multisigOperationInProgress
  | "CannotRespondToOperation" => .multisigCannotRespondToOperation e.error
  | "CannotMarkOperationProcessed" => .multisigCannotMarkOperationProcessed e.error
  | "TransferStatusMismatch" => .multisigTransferStatusMismatch
  | _ => .multisigHubService e.error

end HubError

/-- A cosigner's record of one operation on the hub (`cosigner_op_status`). -/
structure Vote where
  ack : Option Bool := none
  /-- The signed PSBT of an ACK. -/
  psbt : Option FileMetadata := none
  processed : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- An operation the hub stores. -/
structure HubOperation where
  idx : Nat
  initiator : String
  opType : OperationType
  status : OperationStatus
  /-- Files posted with the operation and with the ACKs (`op_file`). -/
  files : List FileMetadata
  /-- Record of every cosigner, in configuration order. -/
  votes : List (String × Vote)
  deriving DecidableEq, Repr, Inhabited

/-- A transfer decision registered on the hub (`TransferStatusInfo`). -/
structure TransferStatusInfo where
  cosignerXpub : String
  accepted : Bool
  registeredAt : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An operation as the hub returns it to a user (`OperationResponse`). -/
structure OperationResponse where
  idx : Nat
  initiator : String
  opType : OperationType
  status : OperationStatus
  /-- Cosigners that ACKed and NACKed, sorted. -/
  ackedBy : List String
  nackedBy : List String
  threshold : Option Nat
  /-- The calling cosigner's answer; `none` for a watch-only user. -/
  myResponse : Option Bool
  processed : Bool
  files : List FileMetadata
  deriving DecidableEq, Repr, Inhabited

/-- What the hub tells about itself (`InfoResponse`, `HubInfo`). -/
structure HubInfo where
  minRgbLibVersion : String := "0.3"
  maxRgbLibVersion : String := "0.3"
  rgbLibVersion : String
  lastOperationIdx : Option Nat
  userRole : UserRole
  deriving DecidableEq, Repr, Inhabited

/-- The hub server's state. -/
structure Hub where
  /-- Colored account xpubs of the cosigners: the hub knows cosigners by them. -/
  cosigners : List String
  thresholdColored : Nat
  thresholdVanilla : Nat
  /-- `major.minor` rgb-lib version every cosigner must run. -/
  rgbLibVersion : String := "0.3"
  /-- Operations in index order; indices start at 1. -/
  operations : List HubOperation := []
  /-- Next free address index of the vanilla (internal) and the colored (external)
  keychain. -/
  nextInternal : Nat := 0
  nextExternal : Nat := 0
  /-- First decision registered per batch transfer index. -/
  transferStatus : List (Nat × TransferStatusInfo) := []
  deriving DecidableEq, Repr, Inhabited

namespace Hub

/-- The hub of a group: the cosigners' colored account xpubs and the thresholds. -/
def ofKeys (k : MultisigKeys) : Hub :=
  { cosigners := k.cosigners.map (·.accountXpubColored), thresholdColored := k.thresholdColored
    thresholdVanilla := k.thresholdVanilla }

/-- Hub rule: a cosigner's token must name a configured cosigner (`Unauthorized`); a
watch-only user is refused on cosigner routes (`Forbidden`). Returns the cosigner. -/
def auth (h : Hub) (u : HubUser) (cosignerRoute : Bool) : Except HubError (Option String) :=
  match u with
  | .cosigner x => if h.cosigners.contains x then .ok (some x) else .error .unauthorized
  | .watchOnly => if cosignerRoute then .error .forbiddenRoute else .ok none

/-- Operation `idx`. -/
def operation? (h : Hub) (idx : Nat) : Option HubOperation :=
  if idx == 0 then none else h.operations[idx - 1]?

/-- Replace an operation. -/
def setOperation (h : Hub) (op : HubOperation) : Hub :=
  { h with operations := h.operations.set (op.idx - 1) op }

/-- Index of the last operation, if any. -/
def lastOperationIdx (h : Hub) : Option Nat :=
  if h.operations.isEmpty then none else some h.operations.length

/-- Threshold of an operation type. -/
def threshold? (h : Hub) (t : OperationType) : Option Nat :=
  t.threshold? h.thresholdColored h.thresholdVanilla

/-- A cosigner's record of an operation. -/
def vote (op : HubOperation) (x : String) : Vote := (op.votes.lookup x).getD {}

/-- Last operation a cosigner marked processed; 0 when none. -/
def lastProcessed (h : Hub) (x : String) : Nat :=
  h.operations.foldl (fun acc op => if (vote op x).processed then max acc op.idx else acc) 0

/-- Hub rule: an operation as a user sees it. The files are the operation's own, ACK
PSBTs included and listed as posted by the initiator, then the ACK PSBTs of the other
cosigners once more. -/
def view (h : Hub) (op : HubOperation) (x : Option String) : OperationResponse :=
  let mine := x.map (vote op)
  let sorted (l : List String) := l.mergeSort fun a b => decide (a ≤ b)
  let byAck (b : Bool) := sorted (op.votes.filterMap fun (c, v) =>
    if v.ack == some b then some c else none)
  { idx := op.idx, initiator := op.initiator, opType := op.opType, status := op.status
    ackedBy := byAck true, nackedBy := byAck false, threshold := h.threshold? op.opType
    myResponse := mine.bind (·.ack), processed := mine.any (·.processed)
    files := op.files ++ op.votes.filterMap fun (c, v) =>
      if c == op.initiator then none else v.psbt }

/-- `GET /info`. -/
def info (h : Hub) (u : HubUser) : Except HubError HubInfo := do
  let x ← h.auth u false
  return { rgbLibVersion := h.rgbLibVersion, lastOperationIdx := h.lastOperationIdx
           userRole := if x.isSome then .cosigner else .watchOnly }

/-- `POST /getoperationbyidx`: the operation, or `none`. -/
def getOperation (h : Hub) (u : HubUser) (idx : Nat) :
    Except HubError (Option OperationResponse) := do
  let x ← h.auth u false
  return (h.operation? idx).map (h.view · x)

/-- `POST /postoperation` (hub rules): one pending operation at a time, and the poster has
processed every operation; the initiator does not count as an ACK. The seed rule is
the one the rgb-lib client states. -/
def postOperation (h : Hub) (u : HubUser) (t : OperationType)
    (files : List (FileType × FileContent)) (seed : Option String) :
    Except HubError (Nat × Hub) := do
  let some x ← h.auth u true | throw .forbiddenRoute
  if h.operations.any (·.status == .pending) then
    throw (.cannotPost "another operation is still pending")
  if h.operations.any fun op => !(vote op x).processed then
    throw (.cannotPost "initiator has unprocessed operations")
  if seed.isSome && !t.requiresSeed then throw (.invalidRequest "unexpected field 'seed'")
  if seed.isNone && t.requiresSeed then throw (.invalidRequest "missing field 'seed'")
  if files.isEmpty then throw (.invalidRequest "no files nor PSBT provided")
  let idx := h.operations.length + 1
  let op : HubOperation :=
    { idx, initiator := x, opType := t, status := if t.autoApproved then .approved else .pending
      files := files.map fun (ft, c) => .ofContent ft x c
      votes := h.cosigners.map fun c => (c, {}) }
  return (idx, { h with operations := h.operations ++ [op] })

/-- `POST /respondtooperation` (hub rules): a cosigner answers once, and only the next
operation it has to process. Approved when the ACKs reach the threshold, discarded when
the NACKs exceed the count minus the threshold (the ACKs can no longer reach it). -/
def respond (h : Hub) (u : HubUser) (idx : Nat) (ack : Bool) (psbt : Option Psbt) :
    Except HubError (OperationResponse × Hub) := do
  let some x ← h.auth u true | throw .forbiddenRoute
  if ack && psbt.isNone then throw (.invalidRequest "ACK requires PSBT file")
  let some op := h.operation? idx | throw .operationNotFound
  if op.status != .pending then throw (.cannotRespond "operation is not pending")
  if (vote op x).ack.isSome then throw (.cannotRespond "already responded to this operation")
  if idx != h.lastProcessed x + 1 then
    throw (.cannotRespond "operation is not the next one to be processed")
  let file := psbt.map fun p => FileMetadata.ofContent .responsePsbt x (.psbt p)
  let votes := op.votes.map fun (c, v) =>
    if c == x then (c, { v with ack := some ack, psbt := file }) else (c, v)
  let acks := (votes.filter (·.2.ack == some true)).length
  let nacks := (votes.filter (·.2.ack == some false)).length
  let t := (h.threshold? op.opType).getD 0
  let status : OperationStatus :=
    if acks ≥ t then .approved else if nacks > h.cosigners.length - t then .discarded else .pending
  let listed := (file.map fun f => { f with postedBy := op.initiator }).toList
  let op := { op with votes, status, files := op.files ++ listed }
  let h := h.setOperation op
  return (h.view op (some x), h)

/-- `POST /markoperationprocessed` (hub rules): not a pending operation, and once. -/
def markProcessed (h : Hub) (u : HubUser) (idx : Nat) : Except HubError Hub := do
  let some x ← h.auth u true | throw .forbiddenRoute
  let some op := h.operation? idx | throw .operationNotFound
  if op.status == .pending then
    throw (.cannotMark "a pending operation cannot be marked as processed")
  let some v := op.votes.lookup x | throw .operationNotFound
  if v.processed then throw (.cannotMark "already marked this operation as processed")
  return h.setOperation { op with votes := op.votes.map fun (c, w) =>
    if c == x then (c, { w with processed := true }) else (c, w) }

/-- `POST /bumpaddressindices` (hub rules): reserve `count` indices of a keychain
(vanilla: internal) and return the first. -/
def bumpAddressIndices (h : Hub) (u : HubUser) (count : Nat) (internal : Bool) :
    Except HubError (Nat × Hub) := do
  let _ ← h.auth u true
  if count > 255 then throw (.invalidRequest "count: expected u8")
  if count == 0 then throw .invalidCount
  if internal then return (h.nextInternal, { h with nextInternal := h.nextInternal + count })
  else return (h.nextExternal, { h with nextExternal := h.nextExternal + count })

/-- `GET /getcurrentaddressindices` (hub rule): the last reserved index of the vanilla
(internal) and the colored (external) keychain. -/
def currentAddressIndices (h : Hub) (u : HubUser) : Except HubError (Option Nat × Option Nat) := do
  let _ ← h.auth u false
  let last (n : Nat) : Option Nat := if n == 0 then none else some (n - 1)
  return (last h.nextInternal, last h.nextExternal)

/-- `POST /transferstatus` without a decision: the registered one, if any. -/
def getTransferStatus (h : Hub) (u : HubUser) (batchIdx : Nat) :
    Except HubError (Option TransferStatusInfo) := do
  let _ ← h.auth u false
  return h.transferStatus.lookup batchIdx

/-- `POST /transferstatus` with a decision (hub rules): cosigners only; the first decision
registered wins, and a different one fails with `TransferStatusMismatch`. -/
def setTransferStatus (h : Hub) (u : HubUser) (batchIdx : Nat) (accept : Bool) (now : Nat) :
    Except HubError (TransferStatusInfo × Hub) := do
  let some x ← h.auth u false | throw .forbidden
  match h.transferStatus.lookup batchIdx with
  | some s => if s.accepted == accept then return (s, h) else throw .transferStatusMismatch
  | none =>
    let s : TransferStatusInfo := { cosignerXpub := x, accepted := accept, registeredAt := now }
    return (s, { h with transferStatus := h.transferStatus ++ [(batchIdx, s)] })

end Hub

/-! ## The wallet side -/

/-- Voting status of an operation, as the wallet reports it (`MultisigVotingStatus`). -/
structure MultisigVotingStatus where
  ackedBy : List String
  nackedBy : List String
  threshold : Nat
  /-- This cosigner's answer, if any. -/
  myResponse : Option Bool
  deriving DecidableEq, Repr, Inhabited

/-- Details of an RGB operation (`SendDetails`, `InflateDetails`, `BurnDetails`). -/
structure OperationDetails where
  /-- The fascia in the `hub_ops` cache. -/
  fasciaPath : String
  minConfirmations : Nat
  entropy : Nat
  /-- Sends only. -/
  isDonation : Bool := false
  /-- Burns only. -/
  burnReason : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- An operation as the wallet reports it (`Operation`). An operation that needs votes
is to review (pending, not answered yet), pending (answered), completed (approved and
executed) or discarded; issuances and receives are completed. -/
inductive Operation where
  | toReview (t : OperationType) (psbt : String) (details : Option OperationDetails)
    (status : MultisigVotingStatus)
  | pending (t : OperationType) (details : Option OperationDetails) (status : MultisigVotingStatus)
  | completed (t : OperationType) (txid : String) (details : Option OperationDetails)
    (status : MultisigVotingStatus)
  | discarded (t : OperationType) (details : Option OperationDetails)
    (status : MultisigVotingStatus)
  | issuanceCompleted (assetId : String)
  | blindReceiveCompleted (details : ReceiveData)
  | witnessReceiveCompleted (details : ReceiveData)
  deriving DecidableEq, Repr, Inhabited

/-- An operation and who initiated it (`OperationInfo`). -/
structure OperationInfo where
  operationIdx : Nat
  initiatorXpub : String
  operation : Operation
  deriving DecidableEq, Repr, Inhabited

/-- An answer to an operation (`RespondToOperation`): an ACK with the signed PSBT, or a NACK. -/
inductive RespondToOperation where
  | ack (psbt : String)
  | nack
  deriving DecidableEq, Repr, Inhabited

/-- What an `_init` returns (`InitOperationResult`): the unsigned PSBT and the index. -/
structure InitOperationResult where
  psbt : String
  operationIdx : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A batch transfer of a wallet, as far as the hub coordination reads it. Cosigners
process operations in the same order, so a transfer has the same index in every
wallet of the group. -/
structure LocalTransfer where
  idx : Nat
  /-- Transaction of an outgoing transfer. -/
  txid : Option String := none
  incoming : Bool
  status : TransferStatus
  deriving DecidableEq, Repr, Inhabited

/-- A multisig wallet: one cosigner's wallet, or a watch-only one. -/
structure Party where
  /-- Hub token: the cosigner's colored account xpub; `none` for a watch-only user. -/
  token : Option String
  /-- Role learned at `go_online`; `none` while offline. -/
  role : Option UserRole := none
  /-- The `backup_info` row: backup times and the last processed operation. -/
  backupInfo : Option DbBackupInfo := none
  /-- Derivation index of the colored and the vanilla keychain (`none`: no address). -/
  coloredIndex : Option Nat := none
  vanillaIndex : Option Nat := none
  /-- Ids of the files cached in `hub_ops`. -/
  cache : List String := []
  /-- Operations executed here, with their transaction. -/
  executed : List (Nat × String) := []
  /-- Imported assets. -/
  assets : List String := []
  transfers : List LocalTransfer := []
  deriving DecidableEq, Repr, Inhabited

namespace Party

/-- The hub user of the wallet's token. -/
def user (p : Party) : HubUser :=
  match p.token with
  | some x => .cosigner x
  | none => .watchOnly

/-- `get_local_last_processed_operation_idx`: the stored sync point, 0 at first. -/
def lastProcessed (p : Party) : Nat := (p.backupInfo.bind (·.lastProcessedOperationIdx)).getD 0

/-- A backup is required (`backup_info`). -/
def backupRequired (p : Party) : Bool := Backup.required p.backupInfo

/-- Index of the next batch transfer. -/
def nextTransferIdx (p : Party) : Nat := p.transfers.length + 1

/-- Store a batch transfer. -/
def addTransfer (p : Party) (t : LocalTransfer) : Party :=
  { p with transfers := p.transfers ++ [t] }

/-- Set the status of a batch transfer. -/
def setStatus (p : Party) (idx : Nat) (s : TransferStatus) : Party :=
  { p with transfers := p.transfers.map fun t =>
      if t.idx == idx then { t with status := s } else t }

/-- Status of a batch transfer. -/
def status? (p : Party) (idx : Nat) : Option TransferStatus :=
  (p.transfers.find? (·.idx == idx)).map (·.status)

/-- Record a state change in `backup_info`, with the index of a processed operation. -/
def record (p : Party) (now : Nat) (idx : Option Nat := none) : Party :=
  { p with backupInfo := some (Backup.update p.backupInfo false now idx) }

/-- The wallet directory as the backup model sees it: the database row and the
`hub_ops` cache. -/
def walletFs (p : Party) (walletDir : String) : Backup.Fs :=
  let ops := Backup.join walletDir "hub_ops"
  let fs := p.cache.foldl (fun fs id => fs.write (Backup.join ops id) (.file id))
    ((Backup.Fs.mk {}).mkdirAll ops)
  match p.backupInfo with
  | some i => Backup.writeInfo fs walletDir i
  | none => fs

end Party

/-- A wallet call: it changes the wallet and the hub; changes made before an error stay. -/
abbrev WalletM := EStateM Error (Party × Hub)

/-- The wallet's state. -/
def party : WalletM Party := return (← get).1
/-- Change the wallet's state. -/
def modifyParty (f : Party → Party) : WalletM Unit := modify fun (p, h) => (f p, h)
/-- A result as a wallet call. -/
def liftR (r : Result α) : WalletM α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

/-- Call the hub as the wallet's user; hub errors map to rgb-lib errors (`map_hub_error`). -/
def hub (f : Hub → HubUser → Except HubError (α × Hub)) : WalletM α := do
  let (p, h) ← get
  match f h p.user with
  | .ok (a, h') => set (p, h'); pure a
  | .error e => throw e.toError

/-- Read from the hub. -/
def hubRead (f : Hub → HubUser → Except HubError α) : WalletM α :=
  hub fun h u => (f h u).map (·, h)

/-- `check_online`: the wallet went online (`offline`). -/
def checkOnline : WalletM Unit := do
  if (← party).role.isNone then throw .offline

/-- `check_is_cosigner`: watch-only users fail with `multisigUserNotCosigner`. -/
def checkIsCosigner : WalletM Unit := do
  if (← party).role != some .cosigner then throw .multisigUserNotCosigner

/-- `multisigUnexpectedData`: hub data the wallet cannot use. -/
def unexpected (d : String) : Error := .multisigUnexpectedData d

/-! ### Going online and addresses -/

/-- `go_online` (multisig part): the hub URL, the token and the hub's `major.minor` rgb-lib
version are checked (`multisigHubService`); the wallet takes its token's role. -/
def goOnline (hubUrl : String) (localVersion : String := "0.3") : WalletM Unit := do
  let valid := ["http://", "https://"].any fun s =>
    hubUrl.startsWith s && !((hubUrl.toList.drop s.length).takeWhile (· ≠ '/')).isEmpty
  if !valid then throw (.multisigHubService "URL must be valid and start with http:// or https://")
  let info ← hubRead fun h u => h.info u
  if localVersion != info.rgbLibVersion then
    throw (.multisigHubService ("rgb-lib version mismatch: " ++
      s!"local version is {localVersion} but hub requires {info.rgbLibVersion}"))
  modifyParty fun p => { p with role := some info.userRole }

/-- `hub_info`: online (watch-only included), then the hub's info. -/
def hubInfo : WalletM HubInfo := do
  checkOnline
  hubRead fun h u => h.info u

/-- Derivation index after revealing `k` more addresses. -/
def reveal (di : Option Nat) (k : Nat) : Option Nat :=
  if k == 0 then di
  else some (match di with
    | none => k - 1
    | some d => d + k)

/-- Address `i` of a keychain of the group's descriptors (symbolic). -/
def addressAt (kind : KeychainKind) (i : Nat) : String :=
  (if kind == .internal then "vanilla/" else "colored/") ++ toString i

/-- `get_new_addresses`: the hub reserves `count` indices and returns the first; the
wallet reveals addresses up to index `first + count` (up to `first + count - 1` when it
had revealed none) and returns address `first`. -/
def newAddresses (kind : KeychainKind) (count : Nat) : WalletM String := do
  let first ← hub fun h u => h.bumpAddressIndices u count (kind == .internal)
  modifyParty fun p =>
    if kind == .internal then
      { p with vanillaIndex := reveal p.vanillaIndex (first + count - p.vanillaIndex.getD 0) }
    else { p with coloredIndex := reveal p.coloredIndex (first + count - p.coloredIndex.getD 0) }
  return addressAt kind first

/-- Address part of `sync_wallet`: each keychain reveals addresses up to the hub's
current index. -/
def syncAddresses : WalletM Unit := do
  let (int, ext) ← hubRead fun h u => h.currentAddressIndices u
  let up (di hi : Option Nat) : Option Nat :=
    match hi, di with
    | some i, some d => some (max d i)
    | some i, none => some i
    | none, d => d
  modifyParty fun p =>
    { p with vanillaIndex := up p.vanillaIndex int, coloredIndex := up p.coloredIndex ext }

/-- `get_address`: online, cosigner, a new vanilla address; a backup becomes required. -/
def getAddress (now : Nat) : WalletM String := do
  checkOnline
  checkIsCosigner
  let a ← newAddresses .internal 1
  modifyParty (·.record now)
  return a

/-! ### Processing operations -/

/-- Hub text of marking an operation a second time. -/
def alreadyMarked : String :=
  "Cannot mark operation as processed: already marked this operation as processed"

/-- Hub part of `mark_operation_as_processed`: a cosigner marks the operation; one it
marked already is fine (other instances of the wallet, restored backups). Watch-only
wallets skip it. The caller then stores the index as the sync point. -/
def markOnHub (idx : Nat) : WalletM Unit := do
  let (p, h) ← get
  if p.role == some .cosigner then
    match h.markProcessed p.user idx with
    | .ok h' => set (p, h')
    | .error e =>
      if e.toError != .multisigCannotMarkOperationProcessed alreadyMarked then throw e.toError

/-- Cache files in `hub_ops`, downloading those missing (`get_or_download_files`). -/
def cacheFiles (files : List FileMetadata) : WalletM Unit :=
  modifyParty fun p => { p with cache := (p.cache ++ files.map (·.fileId)).eraseDups }

/-- The first file of a type. -/
def findFile (files : List FileMetadata) (t : FileType) : Option FileMetadata :=
  files.find? (·.fileType == t)

/-- Path of a cached hub file. -/
def cachePath (id : String) : String := "hub_ops/" ++ id

/-- Operation data of a send, inflation or burn (`InfoBatchTransfer::extract_from_files`). -/
def batchData (files : List FileMetadata) : Result BatchTransferData :=
  match findFile files .operationData with
  | none => .error (unexpected "operation data not found")
  | some f =>
    match f.content with
    | .batchTransfer d => .ok d
    | _ => .error (unexpected "invalid operation data")

/-- Details of an operation (`extract_details`), read before anything else. -/
def extractDetails (t : OperationType) (files : List FileMetadata) :
    Result (Option OperationDetails) := do
  let rgb (tt : TypeOfTransition) (what kind : String) (single : Bool) :
      Result (Option OperationDetails) := do
    let some fascia := findFile files .fascia | throw (unexpected "cannot find fascia")
    let d ← batchData files
    if !d.isOperation tt then throw (unexpected s!"operation data is not of {what}")
    let n := d.transitions.length
    if single && n != 1 then
      throw (unexpected s!"expected 1 transfer for {kind}, got {n} transfers")
    return some { fasciaPath := cachePath fascia.fileId, minConfirmations := d.minConfirmations
                  entropy := d.entropy, isDonation := t == .sendRgb && d.donation
                  burnReason := if t == .burn then d.burnReason else none }
  match t with
  | .sendRgb => rgb .transfer "a send" "send" false
  | .inflation => rgb .inflate "an inflation" "inflation" true
  | .burn => rgb .burn "a burn" "burn" true
  | _ => return none

/-- The operation's unsigned PSBT (`extract_psbt_string`). -/
def operationPsbt (files : List FileMetadata) : Result Psbt :=
  match findFile files .operationPsbt with
  | none => .error (unexpected "PSBT not found")
  | some f =>
    match f.content with
    | .psbt p => .ok p
    | _ => .error (unexpected "invalid PSBT")

/-- Combine the ACK PSBTs (`combine_psbts_from_files`), in file order; at least two. -/
def combinePsbts (files : List FileMetadata) : Result Psbt := do
  let step (acc : Option Psbt × Bool) (f : FileMetadata) : Result (Option Psbt × Bool) := do
    let .psbt p := f.content | throw (unexpected "invalid PSBT")
    match acc.1 with
    | none => return (some p, false)
    | some c =>
      match c.combine? p with
      | some c' => return (some c', true)
      | none => throw .cannotCombinePsbts
  match ← (files.filter (·.fileType == .responsePsbt)).foldlM step (none, false) with
  | (some c, true) => return c
  | _ => throw (unexpected "insufficient PSBTs supplied")

/-- `finalize_psbt_impl`: signatures of `threshold` distinct keys are needed. -/
def finalize (p : Psbt) (threshold : Nat) : Result Unit :=
  if p.signers.eraseDups.length ≥ threshold then .ok () else .error .cannotFinalizePsbt

/-- `build_voting_status`: the hub must give a threshold. -/
def votingStatus (op : OperationResponse) (my : Option Bool) : Result MultisigVotingStatus :=
  match op.threshold with
  | none => .error (unexpected "operation with status should have a threshold")
  | some t =>
    .ok { ackedBy := op.ackedBy, nackedBy := op.nackedBy, threshold := t, myResponse := my }

/-- Execute an approved operation locally (`*_end_impl`); an RGB operation saves an
outgoing transfer. A transfer saved already stays (`cannotEndTransfer` counts as done). -/
def Party.execute (p : Party) (t : OperationType) (idx : Nat) (txid : String)
    (d : Option OperationDetails) : Party :=
  let p := { p with executed := p.executed ++ [(idx, txid)] }
  if !t.isRgb || p.transfers.any (·.txid == some txid) then p
  else
    let status : TransferStatus :=
      if t == .sendRgb && !(d.any (·.isDonation)) then .waitingCounterparty
      else .waitingConfirmations
    p.addTransfer { idx := p.nextTransferIdx, txid := some txid, incoming := false, status }

/-- Process an operation that needs votes (`handle_operation`): an approved one is
executed and marked processed, a discarded one marked processed. -/
def handleOperation (op : OperationResponse) (now : Nat) : WalletM Operation := do
  let files := op.files
  let details ← liftR (extractDetails op.opType files)
  match op.status, op.myResponse with
  | .pending, none =>
    let psbt ← liftR (operationPsbt files)
    return .toReview op.opType psbt.render details (← liftR (votingStatus op none))
  | .pending, some b => return .pending op.opType details (← liftR (votingStatus op (some b)))
  | .approved, _ =>
    let combined ← liftR (combinePsbts files)
    liftR (finalize combined (op.threshold.getD 0))
    if op.opType.isRgb then
      let _ ← liftR (batchData files)
      let some f := findFile files .fascia | throw (unexpected "fascia not found")
      let .fascia _ := f.content | throw (unexpected "invalid fascia")
    markOnHub op.idx
    modifyParty fun p => (p.execute op.opType op.idx combined.txid details).record now (some op.idx)
    return .completed op.opType combined.txid details (← liftR (votingStatus op op.myResponse))
  | .discarded, b =>
    markOnHub op.idx
    modifyParty (·.record now (some op.idx))
    return .discarded op.opType details (← liftR (votingStatus op b))

/-- Import an issuance (`accept_issuance_consignment`): the contract and one media file
per attachment. The model text `invalid contract` stands for the load error. -/
def acceptIssuance (files : List FileMetadata) : Result String := do
  let some f := findFile files .consignment | throw (unexpected "issuance consignment not found")
  let .contract assetId atts := f.content | throw (.internal "invalid contract")
  let media := files.filter (·.fileType == .media)
  if media.length != atts.length then
    throw (unexpected s!"expected {atts.length} media files, got {media.length}")
  for m in media do
    match m.content with
    | .media d => if !atts.contains d then throw (unexpected "media digest mismatch")
    | _ => throw (unexpected "media digest mismatch")
  return assetId

/-- Import a receive (`import_receive_data`); the invoice itself is not checked here. -/
def importReceive (witness : Bool) (files : List FileMetadata) : Result ReceiveMetadata := do
  let some f := findFile files .operationData | throw (unexpected "receive data not found")
  let .receive m := f.content | throw (unexpected "invalid receive data")
  if !witness && m.secretSeal.isNone then throw (unexpected "secret seal not found")
  if (m.seed.bind Hex.toBytes?).isNone then throw (unexpected "invalid operation seed")
  return m

/-- Recipient ID of a witness receive (symbolic: it names the address it pays). -/
def witnessRecipientId (address : String) : String := "wvout:" ++ address

/-- What a receive returns (`ReceiveData`); the public key derives from the seed. -/
def receiveData (m : ReceiveMetadata) (batchIdx : Nat) (witness : Bool) : ReceiveData :=
  { invoice := m.invoice, recipientId := m.recipientId, expirationTimestamp := m.expirationTimestamp
    batchTransferIdx := batchIdx
    publicKey := (Digest.of "ed25519:pk" [encode (m.seed.getD "")]).short
    address := if witness && m.recipientId.startsWith "wvout:" then
        some (String.ofList (m.recipientId.toList.drop 6)) else none }

/-- Whether an operation is legacy (`is_legacy_operation`): a send or receive whose
operation data lacks its operation key. A missing data file is left to the handlers. -/
def isLegacy (op : OperationResponse) : Result Bool :=
  match op.opType.keyName?, findFile op.files .operationData with
  | some key, some f =>
    match f.content.hasKey? key with
    | some b => .ok !b
    | none => .error (unexpected "invalid operation data")
  | _, _ => .ok false

/-- `process_operation`. A legacy operation is never marked processed, so every sync stops
at it. -/
def processOperation (op : OperationResponse) (now : Nat) : WalletM Operation := do
  cacheFiles op.files
  if (← liftR (isLegacy op)) then throw (.multisigLegacyOperation op.idx)
  match op.opType with
  | .issuance =>
    if op.status != .approved then throw (unexpected "unexpected issuance status")
    let assetId ← liftR (acceptIssuance op.files)
    markOnHub op.idx
    modifyParty fun p =>
      ({ p with assets := p.assets ++ [assetId] }.addTransfer
        { idx := p.nextTransferIdx, incoming := true, status := .settled }).record now (some op.idx)
    return .issuanceCompleted assetId
  | .blindReceive | .witnessReceive =>
    if op.status != .approved then throw (unexpected "unexpected receive status")
    let witness := op.opType == .witnessReceive
    let m ← liftR (importReceive witness op.files)
    markOnHub op.idx
    let batchIdx := (← party).nextTransferIdx
    modifyParty fun p => (p.addTransfer { idx := batchIdx, incoming := true
                                          status := .waitingCounterparty }).record now (some op.idx)
    let d := receiveData m batchIdx witness
    return if witness then .witnessReceiveCompleted d else .blindReceiveCompleted d
  | _ => handleOperation op now

/-- `sync_with_hub` (watch-only included): process operation `last + 1`, `last` being the
sync point. A pending operation stays next and is returned again by every sync; an
approved or discarded one moves the sync point and empties the `hub_ops` cache. -/
def syncWithHub (now : Nat) : WalletM (Option OperationInfo) := do
  checkOnline
  syncAddresses
  let next := (← party).lastProcessed + 1
  let some op ← hubRead fun h u => h.getOperation u next | return none
  let operation ← processOperation op now
  if op.status != .pending then modifyParty fun p => { p with cache := [] }
  modifyParty (·.record now)
  return some { operationIdx := op.idx, initiatorXpub := op.initiator, operation }

/-- `respond_to_operation`. Signatures are counted, not verified. The operation the hub
returns is processed here, so an answer that approves or discards it executes or skips
it, without emptying the cache; the hub keeps the answer when that processing fails. -/
def respondToOperation (idx : Nat) (r : RespondToOperation) (now : Nat) :
    WalletM OperationInfo := do
  checkOnline
  checkIsCosigner
  let some op ← hubRead fun h u => h.getOperation u idx | throw (.multisigOperationNotFound idx)
  if op.status != .pending then throw (.multisigCannotRespondToOperation "not pending")
  if op.myResponse.isSome then throw (.multisigCannotRespondToOperation "already responded")
  let psbt? ← match r with
    | .nack => pure none
    | .ack text => do
      let some p := Psbt.parse? text | throw (.invalidPsbt psbtParseError)
      if p.signers.length > Bound.u16 then throw .tooManySignaturesInPsbt
      if p.signers.isEmpty then throw (.invalidPsbt "PSBT has no signatures")
      let some f := findFile op.files .operationPsbt
        | throw (unexpected "operation should have a PSBT")
      cacheFiles [f]
      let .psbt q := f.content | throw (unexpected "invalid PSBT")
      if q.txid != p.txid then throw (.invalidPsbt "PSBT unrelated to operation")
      pure (some p)
  let resp ← hub fun h u => h.respond u idx (r matches .ack _) psbt?
  let operation ← processOperation resp now
  modifyParty (·.record now)
  return { operationIdx := resp.idx, initiatorXpub := resp.initiator, operation }

/-! ### Initiating operations -/

/-- What a `_begin` dry run built: the unsigned PSBT and, for an RGB operation, its
operation data. -/
structure BeginData where
  psbt : Psbt
  data : Option BatchTransferData := none
  deriving DecidableEq, Repr, Inhabited

/-- Common part of the `_init` calls. The `_begin` is a dry run that saves nothing (its
checks are the singlesig ones, not modelled here); a pending operation on the hub, or
one this cosigner has not processed, gives `multisigOperationInProgress`. -/
def initOperation (t : OperationType) (b : BeginData) : WalletM InitOperationResult := do
  checkOnline
  checkIsCosigner
  let rgbFiles : List (FileType × FileContent) :=
    match t.isRgb, b.data with
    | true, some d => [(.fascia, .fascia b.psbt.txid), (.operationData, .batchTransfer d)]
    | _, _ => []
  let seed := if t.requiresSeed then b.data.bind (·.operationSecretKey) else none
  let idx ← hub fun h u => h.postOperation u t (rgbFiles ++ [(.operationPsbt, .psbt b.psbt)]) seed
  return { psbt := b.psbt.render, operationIdx := idx }

/-- `create_utxos_init`. -/
def createUtxosInit (psbt : Psbt) : WalletM InitOperationResult :=
  initOperation .createUtxos ⟨psbt, none⟩
/-- `send_btc_init`. -/
def sendBtcInit (psbt : Psbt) : WalletM InitOperationResult :=
  initOperation .sendBtc ⟨psbt, none⟩
/-- `send_init`; its `_begin` refuses a recipient without transport endpoints
(`unsupportedTransportType`). -/
def sendInit (b : BeginData) : WalletM InitOperationResult := initOperation .sendRgb b
/-- `inflate_init`. -/
def inflateInit (b : BeginData) : WalletM InitOperationResult := initOperation .inflation b
/-- `burn_init`. -/
def burnInit (b : BeginData) : WalletM InitOperationResult := initOperation .burn b

/-- `issue_asset_*`: the contract (made with the singlesig checks) is posted with its
media; the hub approves it at once, and the wallet imports it and marks it processed. -/
def issueAsset (assetId : String) (media : List String := []) (now : Nat) : WalletM String := do
  checkOnline
  checkIsCosigner
  let files := (.consignment, .contract assetId media) :: media.map fun d => (.media, .media d)
  let idx ← hub fun h u => h.postOperation u .issuance files none
  markOnHub idx
  modifyParty fun p =>
    ({ p with assets := p.assets ++ [assetId] }.addTransfer
      { idx := p.nextTransferIdx, incoming := true, status := .settled }).record now (some idx)
  return assetId

/-- A receive request: what `blind_receive` and `witness_receive` take, and the random
operation seed. -/
structure ReceiveRequest where
  invoice : String
  expirationTimestamp : Nat
  transportEndpoints : List String
  minConfirmations : Nat := 1
  /-- Operation seed, hex (random in rgb-lib). -/
  seed : String
  /-- UTXO a blind receive blinds (rgb-lib picks a free one). -/
  utxo : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- `blind_receive` and `witness_receive`: no out-of-band exchange; a witness receive takes
its colored address from the hub. The receive data is posted and approved at once. -/
def receive (witness : Bool) (r : ReceiveRequest) (now : Nat) : WalletM ReceiveData := do
  checkOnline
  checkIsCosigner
  if r.transportEndpoints.isEmpty then throw .unsupportedTransportType
  let recipientId ← if witness then witnessRecipientId <$> newAddresses .external 1
    else pure s!"blind:{r.utxo}"
  let m : ReceiveMetadata :=
    { invoice := r.invoice, recipientId, minConfirmations := r.minConfirmations
      expirationTimestamp := r.expirationTimestamp
      secretSeal := if witness then none else some r.utxo, seed := some r.seed }
  let t : OperationType := if witness then .witnessReceive else .blindReceive
  let idx ← hub fun h u => h.postOperation u t [(.operationData, .receive m)] (some r.seed)
  markOnHub idx
  let batchIdx := (← party).nextTransferIdx
  modifyParty fun p =>
    (p.addTransfer { idx := batchIdx, incoming := true, status := .waitingCounterparty }).record
      now (some idx)
  return receiveData m batchIdx witness

/-! ### Transfer decisions across cosigners -/

/-- `set_hub_accept_status`, before accepting or broadcasting a transfer: a cosigner
registers its acceptance, and fails (`some false`) when a failure came first. A
watch-only wallet follows the registered decision and waits (`none`) without one. -/
def hubAcceptStatus (batchIdx now : Nat) : WalletM (Option Bool) := do
  let (p, h) ← get
  if p.role == some .cosigner then
    match h.setTransferStatus p.user batchIdx true now with
    | .ok (_, h') => set (p, h'); return some true
    | .error e =>
      if e.toError == .multisigTransferStatusMismatch then return some false else throw e.toError
  else
    let s ← hubRead fun h u => h.getTransferStatus u batchIdx
    return s.map (·.accepted)

/-- `get_hub_fail_status`: whether a failure of the transfer is registered. -/
def hubFailStatus (batchIdx : Nat) : WalletM Bool := do
  let s ← hubRead fun h u => h.getTransferStatus u batchIdx
  return s.any (!·.accepted)

/-- `fail_batch_transfer`: a cosigner first registers the failure, which an acceptance
registered before refuses; a watch-only wallet registers nothing. -/
def failBatchTransfer (batchIdx now : Nat) : WalletM Unit := do
  if (← party).role == some .cosigner then
    let _ ← hub fun h u => h.setTransferStatus u batchIdx false now
  modifyParty (·.setStatus batchIdx .failed)

/-- The hub part of refreshing a transfer waiting for its counterparty: a registered
failure fails it; once the counterparty is `ready` (it ACKed, or its consignment came)
the hub decision moves it on, fails it, or keeps it waiting. Returns the new status. -/
def refreshTransfer (batchIdx : Nat) (ready : Bool) (now : Nat) : WalletM TransferStatus := do
  let some t := (← party).transfers.find? (·.idx == batchIdx)
    | throw (.batchTransferNotFound batchIdx)
  if t.status != .waitingCounterparty then return t.status
  if (← hubFailStatus batchIdx) then
    failBatchTransfer batchIdx now
    return .failed
  if !ready then return t.status
  match ← hubAcceptStatus batchIdx now with
  | some true =>
    modifyParty (·.setStatus batchIdx .waitingConfirmations)
    return .waitingConfirmations
  | some false =>
    failBatchTransfer batchIdx now
    return .failed
  | none => return t.status

/-- `fail_transfers` for one batch transfer (cosigners only). -/
def failTransfers (batchIdx now : Nat) : WalletM Unit := do
  checkOnline
  checkIsCosigner
  let some t := (← party).transfers.find? (·.idx == batchIdx)
    | throw (.batchTransferNotFound batchIdx)
  if !t.status.isFallible then throw .cannotFailBatchTransfer
  failBatchTransfer batchIdx now
  modifyParty (·.record now)

/-! ## A group -/

/-- A hub and the wallets that use it, with a clock for backup times. -/
structure Group where
  hub : Hub
  parties : List Party
  now : Nat := 1
  deriving Repr, Inhabited

/-- Party `i`. -/
def Group.party (g : Group) (i : Nat) : Party := g.parties[i]?.getD default

/-- Run a wallet call as party `i`; the clock moves on. Changes made before an error stay. -/
def Group.call (g : Group) (i : Nat) (f : Nat → WalletM α) : Group × Result α :=
  let next (p : Party) (h : Hub) : Group :=
    { hub := h, parties := g.parties.set i p, now := g.now + 1 }
  match (f g.now).run (g.party i, g.hub) with
  | .ok a (p, h) => (next p h, .ok a)
  | .error e (p, h) => (next p h, .error e)

end Multisig

end Rgb.Lib
