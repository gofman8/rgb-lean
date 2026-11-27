import Rgb.Lib.ProxyCrypto
import Rgb.Lib.Constants

/-!
# RGB proxy protocol 1.0

The JSON-RPC protocol rgb-lib uses to exchange consignments, media, ACKs and signed transactions
through proxies (`api/proxy.rs`), and a proxy server as a state machine.

* **Wire**: the methods, their parameters and results, the message each call signs, the error
  codes and how the client maps them to wallet errors (`map_proxy_error`).
* **Client helpers**: how the wallet reads proxy answers (`check_proxy`, `clean_ack_outcome`,
  `sender_proxy_knows_operation`, `proxy_retention_grace`, the proof-of-work retries).
* **Server**: the proxy behaviour the client relies on. A recipient reserves an invoice with an
  expiration and a quota. Senders post consignments to it, one quota slot each. A sender registers
  its operation with the signed transaction encrypted for each recipient. Each recipient ACKs or
  NACKs; once every recipient of the operation has ACKed, the `ack.post` answer releases the
  signed transaction. `ack.clean` revokes the signed transactions of an operation not yet
  released. Data stays for the retention grace after its expiration, then the proxy deletes it.

The proxy server code is not in rgb-lib. Its behaviour here follows what the client expects of
it; where the client does not settle a rule, the model takes the simplest one consistent with the
client, and the rule's comment says it is assumed. The client reads only the code, `data.fields`
and `data.pow_difficulty` of an error; the messages are the model's, except those rgb-lib shows.
-/

namespace Rgb.Lib.Proxy

open Rgb.Lib.ProxyCrypto

/-! ## Methods -/

/-- The JSON-RPC methods of the protocol. -/
inductive Method where
  | serverInfo
  | invoiceCheck
  | invoicePrepare
  | consignmentPost
  | consignmentGet
  | mediaPost
  | mediaGet
  | transferList
  | transferRetrieved
  | transferDelete
  | ackPrepare
  | ackPost
  | ackGet
  | ackClean
  deriving DecidableEq, Repr, Inhabited

namespace Method

/-- Every method. -/
def all : List Method :=
  [serverInfo, invoiceCheck, invoicePrepare, consignmentPost, consignmentGet, mediaPost, mediaGet,
    transferList, transferRetrieved, transferDelete, ackPrepare, ackPost, ackGet, ackClean]

/-- Wire name of the method. -/
def name : Method → String
  | serverInfo => "server.info"
  | invoiceCheck => "invoice.check"
  | invoicePrepare => "invoice.prepare"
  | consignmentPost => "consignment.post"
  | consignmentGet => "consignment.get"
  | mediaPost => "media.post"
  | mediaGet => "media.get"
  | transferList => "transfer.list"
  | transferRetrieved => "transfer.retrieved"
  | transferDelete => "transfer.delete"
  | ackPrepare => "ack.prepare"
  | ackPost => "ack.post"
  | ackGet => "ack.get"
  | ackClean => "ack.clean"

/-- Multipart calls, which upload a file besides their parameters. -/
def uploadsFile : Method → Bool
  | consignmentPost | mediaPost | ackPrepare => true
  | _ => false

/-- Calls that start a new transfer, which a draining proxy refuses. -/
def startsTransfer : Method → Bool
  | invoicePrepare | consignmentPost | ackPrepare => true
  | _ => false

end Method

/-- Key that signs a call's message. -/
inductive Signer where
  /-- The sender's operation key. -/
  | sender
  /-- The recipient's operation key. -/
  | recipient
  /-- The caller's proxy authentication key, sent only when one is configured for the proxy. -/
  | proxyAuth
  deriving DecidableEq, Repr, Inhabited

/-- Signer of each call, if it is signed. -/
def Method.signer? : Method → Option Signer
  | .consignmentPost | .mediaPost | .ackGet | .ackClean => some .sender
  | .ackPost | .transferList | .transferRetrieved | .transferDelete => some .recipient
  | .invoicePrepare | .ackPrepare => some .proxyAuth
  | .serverInfo | .invoiceCheck | .consignmentGet | .mediaGet => none

/-! ## Parameters and results -/

/-- `invoice.check` status of an invoice (`InvoiceStatus`). -/
inductive InvoiceStatus where
  /-- Not reserved, or its data was deleted. -/
  | unknown
  /-- Reserved and below its quota. -/
  | available
  /-- Reserved and its quota reached. -/
  | full
  deriving DecidableEq, Repr, Inhabited

/-- `transfer.list` state of a transfer (`ProxyTransferState`). -/
inductive TransferListStatus where
  /-- Its consignment and media can be downloaded. -/
  | pending
  /-- Its data was deleted by `transfer.retrieved`. -/
  | retrieved
  deriving DecidableEq, Repr, Inhabited

/-- `server.info` result (`ServerInfoResponse`); the client parses the optional fields. -/
structure ServerInfo where
  protocolVersion : String
  /-- Software version of the proxy. -/
  version : String
  /-- Seconds since the proxy started. -/
  uptime : Nat
  /-- Unix time of the proxy's clock. -/
  currentTime : Option String := none
  /-- Furthest expiration accepted, in seconds from now. -/
  maxExpirySecs : Option String := none
  maxQuota : Option String := none
  maxPowDifficulty : Option String := none
  /-- How long after an expiration the proxy keeps the data awaiting retrieval. -/
  retentionGraceSecs : Option String := none
  /-- Most media per transfer. -/
  maxMedia : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- One `invoice.check` answer (`InvoiceCheckResponse`). -/
structure InvoiceCheck where
  status : InvoiceStatus
  /-- Proof of work a `consignment.post` to the invoice needs, in leading zero bits. -/
  powDifficulty : String
  deriving DecidableEq, Repr, Inhabited

/-- `consignment.post` parameters and file; `file_size` is `file.len`. -/
structure ConsignmentPost where
  invoiceId : String
  transferId : String
  /-- Sender proxy endpoint (`rpc://` form) where the recipient posts its ACK. -/
  senderTransportEndpoint : String
  senderPk : String
  /-- Hex SHA-256 of the plaintext consignment file. -/
  consignmentHash : String
  /-- Whether the operation has other recipients. -/
  batch : Bool
  /-- Sender signature of `Msg.postConsignment`. -/
  signature : Ed25519Sig
  /-- Unix time the proof of work is computed for. -/
  powTimestamp : Nat
  powNonce : String
  /-- The consignment, encrypted unless the recipient does not support encryption. -/
  file : Blob
  deriving DecidableEq, Repr, Inhabited

/-- `consignment.get` result (`GetConsignmentResponse`). -/
structure ConsignmentGetResult where
  consignment : Blob
  senderTransportEndpoint : String
  senderPk : String
  consignmentHash : String
  batch : Bool
  deriving DecidableEq, Repr, Inhabited

/-- `media.post` parameters and file; `file_size` is `file.len`. -/
structure MediaPost where
  transferId : String
  /-- `DerivedKeys.mediaId` of the media's digest. -/
  mediaId : String
  /-- Sender signature of `Msg.postMedia`. -/
  signature : Ed25519Sig
  file : Blob
  deriving DecidableEq, Repr, Inhabited

/-- What `ack.prepare` registers for one transfer (`AckTransferData`). -/
structure AckTransferData where
  recipientPk : String
  consignmentHash : String
  /-- The signed transaction encrypted for the recipient (in the uploaded `signed_txs.json`). -/
  signedTx : Blob
  deriving DecidableEq, Repr, Inhabited

/-- `ack.prepare` parameters and file; `file_size` is the size of `signed_txs.json`. -/
structure AckPrepare where
  /-- Data of each transfer of the operation, by transfer id. -/
  transferData : List (String × AckTransferData)
  /-- Operation expiration (Unix time). -/
  expiresAt : Nat
  /-- Hex SHA-256 of the signed transaction. -/
  signedTxHash : String
  senderPk : String
  /-- Proxy authentication signature of `Msg.prepareAckAuth`, sent when configured. -/
  signature : Option Ed25519Sig := none
  deriving DecidableEq, Repr, Inhabited

/-- `ack.post` result (`PostAckResponse`). -/
structure PostAckResponse where
  result : Bool
  /-- The sender's public key, with the released transaction. -/
  senderPk : Option String := none
  /-- The released signed transaction, encrypted for this recipient. -/
  signedTx : Option Blob := none
  signedTxHash : Option String := none
  /-- The operation expiration, in decimal. -/
  expiresAt : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- `ack.get` result (`GetAckResponse`); transfers not answered yet are absent. -/
structure AckGetResult where
  acks : List (String × Bool)
  signatures : List (String × Ed25519Sig)
  deriving DecidableEq, Repr, Inhabited

/-! ## Signed messages

Each signed call signs the hash of its message (`‖` is concatenation), with the key
`Method.signer?` names. -/

namespace Msg

/-- Ids in lexicographic order, concatenated. -/
def sortedConcat (ids : List String) : String :=
  String.join (ids.mergeSort fun a b => compare a b != .gt)

/-- `consignment.post`: `transfer_id ‖ consignment_hash ‖ blob_hash ‖ "consignment"`. -/
def postConsignment (transferId consignmentHash blobHash : String) : String :=
  transferId ++ consignmentHash ++ blobHash ++ "consignment"

/-- `media.post`: `transfer_id ‖ media_id ‖ blob_hash ‖ "media"`. -/
def postMedia (transferId mediaId blobHash : String) : String :=
  transferId ++ mediaId ++ blobHash ++ "media"

/-- `transfer.list`: `invoice_id ‖ timestamp`. -/
def listTransfers (invoiceId timestamp : String) : String := invoiceId ++ timestamp

/-- `ack.get`: the sorted transfer ids, then the timestamp. -/
def getAck (transferIds : List String) (timestamp : String) : String :=
  sortedConcat transferIds ++ timestamp

/-- `ack.clean`: the sorted transfer ids. -/
def cleanAck (transferIds : List String) : String := sortedConcat transferIds

/-- `ack.post`: `transfer_id ‖ "true" | "false" ‖ consignment_hash`. -/
def ack (transferId : String) (ack : Bool) (consignmentHash : String) : String :=
  transferId ++ toString ack ++ consignmentHash

/-- `transfer.retrieved`: `transfer_id ‖ "retrieved"`. -/
def transferRetrieved (transferId : String) : String := transferId ++ "retrieved"

/-- `transfer.delete`: `transfer_id ‖ "delete"`. -/
def deleteTransfer (transferId : String) : String := transferId ++ "delete"

/-- `invoice.prepare` proxy authentication: `invoice_id ‖ expires_at ‖ recipient_pk ‖ quota`. -/
def prepareInvoiceAuth (invoiceId expiresAt recipientPk : String) (quota : Nat) : String :=
  invoiceId ++ expiresAt ++ recipientPk ++ toString quota

/-- `ack.prepare` proxy authentication: `sender_pk ‖ expires_at ‖ signed_tx_hash`, then
`transfer_id ‖ recipient_pk ‖ consignment_hash` per transfer in transfer id order. -/
def prepareAckAuth (senderPk expiresAt signedTxHash : String)
    (transferData : List (String × AckTransferData)) : String :=
  let sorted := transferData.mergeSort fun a b => compare a.1 b.1 != .gt
  senderPk ++ expiresAt ++ signedTxHash ++
    String.join (sorted.map fun (tid, d) => tid ++ d.recipientPk ++ d.consignmentHash)

end Msg

/-- A sender's `consignment.post` to an invoice: the transfer id derived from the invoice and the
sender key, the signature over the uploaded file. -/
def ConsignmentPost.make (sender : SecretKey) (invoiceId senderTransportEndpoint
    consignmentHash : String) (batch : Bool) (file : Blob) (powTimestamp : Nat)
    (powNonce : String := "0") : ConsignmentPost :=
  let tid := ProxyCrypto.transferId invoiceId sender.pk
  { invoiceId, transferId := tid, senderTransportEndpoint, senderPk := sender.pk,
    consignmentHash, batch, powTimestamp, powNonce, file
    signature := signMessage sender (Msg.postConsignment tid consignmentHash file.hash) }

/-- A sender's `media.post`, signed over the uploaded file. -/
def MediaPost.make (sender : SecretKey) (transferId mediaId : String) (file : Blob) : MediaPost :=
  { transferId, mediaId, file
    signature := signMessage sender (Msg.postMedia transferId mediaId file.hash) }

/-- What a sender registers for one recipient: the signed transaction encrypted with their
shared key. -/
def AckTransferData.make (sender : SecretKey) (recipientPk consignmentHash : String) (tx : Tx) :
    AckTransferData :=
  { recipientPk, consignmentHash
    signedTx := Blob.encrypt (.tx tx) (deriveShared sender recipientPk).symKey }

/-- `posted_by_sender`: a downloaded transfer is the one its sender key derives. -/
def postedBySender (invoiceId transferId : String) (r : ConsignmentGetResult) : Bool :=
  ProxyCrypto.transferId invoiceId r.senderPk == transferId

/-- A recipient's signature of its answer to a transfer. -/
def ackSignature (recipient : SecretKey) (transferId : String) (ack : Bool)
    (consignmentHash : String) : Ed25519Sig :=
  signMessage recipient (Msg.ack transferId ack consignmentHash)

/-! ## Errors -/

/-- A JSON-RPC error (`JsonRpcError`). Non-string entries of `data.fields` are not modelled. -/
structure JsonRpcError where
  code : Int
  message : String
  /-- `data.fields`: the offending parameters of -100, -200 and -300 errors (empty if absent). -/
  fields : List String := []
  /-- `data.pow_difficulty` of a -114 error. -/
  powDifficulty : Option String := none
  deriving DecidableEq, Repr, Inhabited

namespace JsonRpcError

/-- `details()`: the message, followed by the offending fields when there are some. -/
def details (e : JsonRpcError) : String :=
  if e.fields.isEmpty then e.message else e.message ++ ": " ++ String.intercalate ", " e.fields

/-- `has_field`: `f` is among the offending fields. -/
def hasField (e : JsonRpcError) (f : String) : Bool := e.fields.contains f

/-- `only_field`: `f` is the only offending field. -/
def onlyField (e : JsonRpcError) (f : String) : Bool := e.fields == [f]

end JsonRpcError

/-! Error codes of the protocol. -/
namespace Code
/-- Change of data the proxy already stores (`data.fields` names it). -/
def cannotChange : Int := -100
/-- The invoice is not reserved. -/
def invoiceNotReserved : Int := -101
/-- The transfer id belongs to another operation. -/
def transferIdInUse : Int := -102
/-- No operation registers the transfer. -/
def operationNotFound : Int := -104
/-- The operation expired without releasing its transaction. -/
def operationExpired : Int := -105
/-- The transaction was released, so it cannot be revoked. -/
def txAlreadyReleased : Int := -107
/-- The invoice has expired. -/
def invoiceExpired : Int := -111
/-- The invoice has no quota slot left. -/
def invoiceQuotaExceeded : Int := -112
/-- The transfer id was deleted and cannot be posted again. -/
def transferIdDeleted : Int := -113
/-- The proof of work misses the difficulty in `data.pow_difficulty`. -/
def invalidPow : Int := -114
/-- The proxy is draining. -/
def draining : Int := -115
/-- The transfer has the most media the proxy accepts. -/
def tooManyMedia : Int := -116
/-- An invalid parameter (`data.fields` names it). -/
def invalid : Int := -200
/-- A missing parameter (`data.fields` names it). -/
def missing : Int := -300
/-- A missing file. -/
def missingFile : Int := -301
/-- No consignment for the transfer. -/
def consignmentNotFound : Int := -400
/-- No such media for the transfer. -/
def mediaNotFound : Int := -401
/-- The consignment was retrieved and deleted. -/
def consignmentRetrieved : Int := -402
/-- The transfer was deleted. -/
def consignmentDeleted : Int := -403
/-- Invalid proxy authentication signature. -/
def invalidProxyAuth : Int := -501
/-- Invalid signature of an authenticated endpoint. -/
def invalidEndpointAuth : Int := -502
/-- Invalid signature of posted content. -/
def invalidContentSignature : Int := -503
end Code

/-- Codes the client maps to one wallet error whatever their data. -/
def codeErrors : List (Int × Error) :=
  [ (Code.invoiceNotReserved, .invoiceNotReserved), (Code.transferIdInUse, .transferIdInUse),
    (Code.operationNotFound, .operationNotFound), (Code.operationExpired, .operationExpired),
    (Code.txAlreadyReleased, .proxyTxAlreadyReleased), (Code.invoiceExpired, .invoiceExpired),
    (Code.invoiceQuotaExceeded, .invoiceQuotaExceeded),
    (Code.transferIdDeleted, .transferIdDeleted), (Code.draining, .proxyDraining),
    (Code.tooManyMedia, .proxyTooManyMedia), (Code.consignmentNotFound, .noConsignment),
    (Code.mediaNotFound, .noMedia), (Code.consignmentRetrieved, .noConsignment),
    (Code.consignmentDeleted, .noConsignment),
    (Code.invalidProxyAuth, .invalidProxyAuthSignature),
    (Code.invalidEndpointAuth, .invalidEndpointAuthSignature),
    (Code.invalidContentSignature, .invalidContentSignature) ]

/-- `map_proxy_error`: -100 with `signed_tx` as its only field means the signed transaction was
cleared; -200 naming `expires_at` is an invalid expiration; other codes outside `codeErrors`
(-114 included) keep their details. -/
def mapProxyError (e : JsonRpcError) : Error :=
  if e.code == Code.cannotChange then
    if e.onlyField "signed_tx" then .signedTxCleared else .proxyCannotChange e.details
  else if e.code == Code.invalid && e.hasField "expires_at" then .expirationInvalid
  else (codeErrors.lookup e.code).getD (.proxy e.details)

/-- Value of decimal digits, if there is at least one and nothing else. -/
def digitsValue? (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)

/-- Rust's `str::parse` of a `bits`-bit unsigned integer: an optional `+`, then digits. -/
def parseUnsigned? (s : String) (bits : Nat) : Option Nat :=
  let cs := match s.toList with
    | '+' :: rest => rest
    | cs => cs
  (digitsValue? cs).filter (· < 2 ^ bits)

/-- Rust's `str::parse::<i64>`: an optional sign, then digits. -/
def parseI64? (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (digitsValue? cs).bind fun n => if n ≤ 2 ^ 63 then some (-(n : Int)) else none
  | '+' :: cs => (digitsValue? cs).bind fun n => if n < 2 ^ 63 then some (n : Int) else none
  | cs => (digitsValue? cs).bind fun n => if n < 2 ^ 63 then some (n : Int) else none

/-- `pow_difficulty_required`: the difficulty a -114 error asks for, if it parses as a `u32`. -/
def powDifficultyRequired (e : JsonRpcError) : Option Nat :=
  if e.code == Code.invalidPow then e.powDifficulty.bind (parseUnsigned? · 32) else none

/-! ## Client helpers -/

/-- A JSON-RPC response (`JsonRpcResponse`): a result, an error, or neither. -/
structure Response (α : Type) where
  result : Option α := none
  error : Option JsonRpcError := none
  deriving DecidableEq, Repr

/-- `check_proxy`: the proxy must speak `proxyProtocolVersion`; without a result the error
message (not its mapping) is the details. -/
def checkProxy (r : Response ServerInfo) : Except Error ServerInfo :=
  match r.result with
  | some info =>
    if info.protocolVersion == proxyProtocolVersion then .ok info
    else .error (.invalidProxyProtocol info.protocolVersion)
  | none =>
    .error (.proxy ((r.error.map (·.message)).getD "proxy response has neither result nor error"))

/-- `proxy_retention_grace`: the advertised `retention_grace_secs`, or 0 when absent or not a
`u32`. -/
def proxyRetentionGrace (info : ServerInfo) : Nat :=
  (info.retentionGraceSecs.bind (parseUnsigned? · 32)).getD 0

/-- `proxy_max_media`: the advertised `max_media`, if it is a `usize`. -/
def proxyMaxMedia (info : ServerInfo) : Option Nat := info.maxMedia.bind (parseUnsigned? · 64)

/-- `sender_proxy_retention_grace`, from the sender proxy's `server.info` response; it does not
check the protocol version. -/
def senderProxyRetentionGrace (r : Response ServerInfo) : Except Error Nat :=
  match r.error, r.result with
  | some e, _ => .error (mapProxyError e)
  | none, none => .error (.proxy "missing server.info result")
  | none, some info => .ok (proxyRetentionGrace info)

/-- What an `ack.clean` answer means for a deliberate fail (`CleanAckOutcome`). -/
inductive CleanAckOutcome where
  /-- The signed transactions were revoked: nothing can be released anymore. -/
  | revoked
  /-- The transaction was already released to a recipient, who may still broadcast it. -/
  | released
  /-- The proxy does not know the operation: whether it released the transaction is unknown. -/
  | unknown
  deriving DecidableEq, Repr, Inhabited

/-- `clean_ack_outcome`, on the mapped error of the `ack.clean` answer. -/
def cleanAckOutcome : Option Error → Except Error CleanAckOutcome
  | none => .ok .revoked
  | some .proxyTxAlreadyReleased => .ok .released
  | some .operationNotFound => .ok .unknown
  | some e => .error e

/-- `check_get_ack_error`: of the `ack.get` errors only `operationNotFound` is settled on. -/
def checkGetAckError : Error → Except Error Unit
  | .operationNotFound => .ok ()
  | e => .error e

/-- `sender_proxy_knows_operation`, on the mapped error of the `ack.get` answer. -/
def senderProxyKnowsOperation : Option Error → Except Error Bool
  | none => .ok true
  | some .operationNotFound => .ok false
  | some e => .error e

/-- The error of a result, if any. -/
def errorOf? {ε α : Type} : Except ε α → Option ε
  | .ok _ => none
  | .error e => some e

/-! ## Server -/

/-- Furthest expiration a proxy accepts by default, in seconds from now (30 days). -/
def defaultMaxExpirySecs : Nat := 30 * 24 * 60 * 60
/-- Largest invoice quota the model proxy accepts by default (assumed). -/
def defaultMaxQuota : Nat := 100
/-- Media per transfer the model proxy accepts by default: a UDA token's media and attachments
(assumed). -/
def defaultMaxMedia : Nat := maxAttachments + 1
/-- Tolerance the proxy applies to request timestamps. -/
def timestampToleranceSecs : Nat := proxyClockSkewMarginSecs
/-- `consignment.post` attempts with a new proof of work (`MAX_POW_ATTEMPTS`). -/
def maxPowAttempts : Nat := 3
/-- Software version the model proxy reports. -/
def serverVersion : String := "model"

/-- What a proxy is configured with; `server.info` advertises it. -/
structure Config where
  /-- How long after an expiration the proxy keeps invoices, transfers and operations. -/
  retentionGraceSecs : Nat
  /-- Furthest expiration accepted, in seconds from now. -/
  maxExpirySecs : Nat := defaultMaxExpirySecs
  maxQuota : Nat := defaultMaxQuota
  maxMedia : Nat := defaultMaxMedia
  /-- Proof of work `consignment.post` needs, in leading zero bits. -/
  powDifficulty : Nat := 0
  /-- A draining proxy refuses the calls that start a new transfer. -/
  draining : Bool := false
  /-- Public key whose signature `invoice.prepare` and `ack.prepare` need, if any. -/
  authPk : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- `server.info` of a proxy with this configuration; `max_pow_difficulty` is the current
difficulty (assumed). -/
def Config.advertise (c : Config) (now uptime : Nat) : ServerInfo :=
  { protocolVersion := proxyProtocolVersion, version := serverVersion, uptime
    currentTime := some (toString now)
    maxExpirySecs := some (toString c.maxExpirySecs)
    maxQuota := some (toString c.maxQuota)
    maxPowDifficulty := some (toString c.powDifficulty)
    retentionGraceSecs := some (toString c.retentionGraceSecs)
    maxMedia := some (toString c.maxMedia) }

/-- A reserved invoice. -/
structure InvoiceRecord where
  expiresAt : Nat
  recipientPk : String
  quota : Nat
  /-- Transfers posted to it and not deleted, in posting order: one quota slot each. -/
  transfers : List String := []
  deriving DecidableEq, Repr, Inhabited

/-- A posted transfer. -/
structure TransferRecord where
  invoiceId : String
  senderTransportEndpoint : String
  senderPk : String
  consignmentHash : String
  batch : Bool
  /-- `blob_hash` of the posted file. -/
  blobHash : String
  /-- The posted file, until `transfer.retrieved`. -/
  consignment : Option Blob
  /-- Posted media by media id, until `transfer.retrieved`. -/
  media : List (String × Blob) := []
  deriving DecidableEq, Repr, Inhabited

/-- One transfer of a registered operation. -/
structure AckRecord where
  recipientPk : String
  consignmentHash : String
  /-- The signed transaction encrypted for the recipient, until `ack.clean`. -/
  signedTx : Option Blob
  /-- The recipient's answer: `true` for an ACK, `false` for a NACK. -/
  ack : Option Bool := none
  /-- The recipient's signature of its answer. -/
  signature : Option Ed25519Sig := none
  deriving DecidableEq, Repr, Inhabited

/-- An operation registered by `ack.prepare`, keyed by its sender (operation) public key. -/
structure OperationRecord where
  senderPk : String
  expiresAt : Nat
  signedTxHash : String
  transfers : OrdMap String AckRecord
  /-- Set once every recipient has ACKed while the signed transactions are in place. -/
  released : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The `ack.post` answer to a transfer of the operation: the operation expiration, and the
signed transaction once released, for a recipient that ACKed. -/
def OperationRecord.answer (op : OperationRecord) (r : AckRecord) : PostAckResponse :=
  if op.released && r.ack == some true then
    { result := true, senderPk := some op.senderPk, signedTx := r.signedTx
      signedTxHash := some op.signedTxHash, expiresAt := some (toString op.expiresAt) }
  else { result := true, expiresAt := some (toString op.expiresAt) }

/-- A proxy server. -/
structure Server where
  url : String
  /-- The proxy's clock (Unix time). -/
  now : Nat
  /-- What `server.info` returns. -/
  info : ServerInfo
  config : Config
  /-- Unix time the proxy started. -/
  startedAt : Nat
  /-- Reserved invoices by invoice id. -/
  invoices : OrdMap String InvoiceRecord := {}
  /-- Posted transfers by transfer id. -/
  transfers : OrdMap String TransferRecord := {}
  /-- Transfer ids deleted by `transfer.delete`, which cannot be posted again. -/
  deleted : List String := []
  /-- Registered operations by sender public key. -/
  operations : OrdMap String OperationRecord := {}
  deriving DecidableEq, Repr, Inhabited

namespace Server

/-- A proxy started at `now`, advertising its whole configuration. -/
def init (url : String) (now : Nat) (retentionGraceSecs : Nat := 86400) : Server :=
  let config : Config := { retentionGraceSecs }
  { url, now, config, startedAt := now, info := config.advertise now 0 }

/-- Change the configuration, and what `server.info` advertises with it. -/
def configure (s : Server) (f : Config → Config) : Server :=
  let config := f s.config
  { s with config, info := config.advertise s.now (s.now - s.startedAt) }

/-- `server.info`: always answered. -/
def serverInfo (s : Server) : Response ServerInfo := { result := some s.info }

/-- Whether a request timestamp lies within the proxy's tolerance of its clock (assumed for the
proof-of-work timestamp). -/
def fresh (s : Server) (t : Nat) : Bool :=
  s.now ≤ t + timestampToleranceSecs && t ≤ s.now + timestampToleranceSecs

/-- Whether an expiration is accepted: not past, and at most `maxExpirySecs` ahead. -/
def validExpiry (s : Server) (e : Nat) : Bool := s.now ≤ e && e ≤ s.now + s.config.maxExpirySecs

/-- The operation registering every one of `ids`, if one does. -/
def operationOf? (s : Server) (ids : List String) : Option OperationRecord :=
  match ids with
  | [] => none
  | tid :: _ =>
    (s.operations.values.find? (·.transfers.contains tid)).filter fun op =>
      ids.all op.transfers.contains

/-- Recipient key of a posted transfer: the key of the invoice it pays. -/
def recipientPkOf? (s : Server) (transferId : String) : Option String := do
  let t ← s.transfers.find? transferId
  let inv ← s.invoices.find? t.invoiceId
  return inv.recipientPk

/-- Status of an invoice: unknown unless reserved, full once its quota is taken. An expired
invoice keeps its status until deleted (assumed). -/
def invoiceStatus (s : Server) (invoiceId : String) : InvoiceStatus :=
  match s.invoices.find? invoiceId with
  | none => .unknown
  | some inv => if inv.quota ≤ inv.transfers.length then .full else .available

/-- `invoice.check`, with the proof of work each invoice needs. -/
def invoiceCheckFull (s : Server) (invoiceIds : List String) : List (String × InvoiceCheck) :=
  invoiceIds.map fun id => (id, ⟨s.invoiceStatus id, toString s.config.powDifficulty⟩)

/-- `invoice.check`: the status of each invoice. -/
def invoiceCheck (s : Server) (invoiceIds : List String) : List (String × InvoiceStatus) :=
  invoiceIds.map fun id => (id, s.invoiceStatus id)

/-- Advance the clock by `secs`. An invoice (with its transfers) or an operation is deleted as
soon as its expiration plus the retention grace has passed (assumed). -/
def tick (s : Server) (secs : Nat) : Server :=
  let now := s.now + secs
  let kept (expiresAt : Nat) : Bool := now ≤ expiresAt + s.config.retentionGraceSecs
  let invoices := s.invoices.filter fun _ inv => kept inv.expiresAt
  { s with
    now
    info := { s.info with currentTime := some (toString now), uptime := now - s.startedAt }
    invoices
    transfers := s.transfers.filter fun _ t => invoices.contains t.invoiceId
    operations := s.operations.filter fun _ op => kept op.expiresAt }

end Server

/-! ## Server calls on the wire

Each call returns the JSON-RPC error the proxy answers with. The checks run in the order
written; where the client does not settle the order or the code of a check, they are assumed. -/

namespace Err

/-- Message of each code without fields. -/
def message (code : Int) : String :=
  if code == Code.invoiceNotReserved then "Invoice not reserved"
  else if code == Code.transferIdInUse then "Transfer ID in use"
  else if code == Code.operationNotFound then "Operation not found"
  else if code == Code.operationExpired then "Operation expired"
  else if code == Code.txAlreadyReleased then "TX already released"
  else if code == Code.invoiceExpired then "Invoice expired"
  else if code == Code.invoiceQuotaExceeded then "Invoice quota exceeded"
  else if code == Code.transferIdDeleted then "Transfer ID deleted"
  else if code == Code.invalidPow then "Invalid proof of work"
  else if code == Code.draining then "Server draining"
  else if code == Code.tooManyMedia then "Too many media"
  else if code == Code.consignmentNotFound then "Consignment not found"
  else if code == Code.mediaNotFound then "Media not found"
  else if code == Code.consignmentRetrieved then "Consignment retrieved"
  else if code == Code.consignmentDeleted then "Consignment deleted"
  else if code == Code.invalidProxyAuth then "Invalid proxy auth signature"
  else if code == Code.invalidEndpointAuth then "Invalid endpoint auth signature"
  else if code == Code.invalidContentSignature then "Invalid content signature"
  else "Error"

/-- An error with its code's message. -/
def code (c : Int) : JsonRpcError := { code := c, message := message c }

/-- -100 for the changed fields. -/
def cannotChange (fields : List String) : JsonRpcError :=
  { code := Code.cannotChange, message := "Cannot change", fields }

/-- -200 for the invalid fields. -/
def invalid (fields : List String) : JsonRpcError :=
  { code := Code.invalid, message := "Invalid", fields }

/-- -300 for the missing fields (the message rgb-lib shows). -/
def missing (fields : List String) : JsonRpcError :=
  { code := Code.missing, message := "Missing", fields }

/-- -114 with the difficulty the proxy needs. -/
def invalidPow (difficulty : Nat) : JsonRpcError :=
  { code Code.invalidPow with powDifficulty := some (toString difficulty) }

end Err

/-- Names of the fields whose flag is set. -/
def changedFields (l : List (String × Bool)) : List String :=
  l.filterMap fun (f, c) => if c then some f else none

namespace Wire

open Server

/-- A draining proxy refuses the calls that start a new transfer. -/
def checkDraining (s : Server) (m : Method) : Except JsonRpcError Unit :=
  if s.config.draining && m.startsTransfer then throw (Err.code Code.draining) else pure ()

/-- With a proxy authentication key configured, the call must carry its signature of
`message`. -/
def checkProxyAuth (s : Server) (signature : Option Ed25519Sig) (message : String) :
    Except JsonRpcError Unit :=
  match s.config.authPk, signature with
  | none, _ => pure ()
  | some _, none => throw (Err.missing ["signature"])
  | some pk, some sig =>
    if verifyMessage pk message sig then pure () else throw (Err.code Code.invalidProxyAuth)

/-- `invoice.prepare`: reserve an invoice. The quota bounds, and that the same reservation again
changes nothing while another one is a change, are assumed. -/
def invoicePrepare (s : Server) (invoiceId : String) (expiresAt : Nat) (recipientPk : String)
    (quota : Nat) (signature : Option Ed25519Sig := none) : Except JsonRpcError Server := do
  checkDraining s .invoicePrepare
  checkProxyAuth s signature
    (Msg.prepareInvoiceAuth invoiceId (toString expiresAt) recipientPk quota)
  unless s.validExpiry expiresAt do throw (Err.invalid ["expires_at"])
  unless 0 < quota && quota ≤ s.config.maxQuota do throw (Err.invalid ["quota"])
  match s.invoices.find? invoiceId with
  | some inv =>
    let changed := changedFields [("expires_at", inv.expiresAt != expiresAt),
      ("recipient_pk", inv.recipientPk != recipientPk), ("quota", inv.quota != quota)]
    unless changed.isEmpty do throw (Err.cannotChange changed)
    return s
  | none =>
    return { s with invoices := s.invoices.insert invoiceId { expiresAt, recipientPk, quota } }

/-- Fields of a `consignment.post` that differ from the stored transfer. -/
def changedPostFields (t : TransferRecord) (p : ConsignmentPost) (blobHash : String) :
    List String :=
  changedFields [("invoice_id", t.invoiceId != p.invoiceId),
    ("sender_transport_endpoint", t.senderTransportEndpoint != p.senderTransportEndpoint),
    ("sender_pk", t.senderPk != p.senderPk), ("consignment_hash", t.consignmentHash !=
      p.consignmentHash), ("batch", t.batch != p.batch), ("file", t.blobHash != blobHash)]

/-- `consignment.post`: store a consignment for a transfer to a reserved invoice, taking one of
its quota slots. The proxy checks the sender's signature but not that the transfer id derives
from the invoice and the sender key, which the recipient checks; a repeat changes nothing (all
three assumed). -/
def consignmentPost (s : Server) (p : ConsignmentPost) : Except JsonRpcError Server := do
  checkDraining s .consignmentPost
  unless s.fresh p.powTimestamp do throw (Err.invalid ["pow_timestamp"])
  unless powMeets p.transferId (toString p.powTimestamp) p.powNonce s.config.powDifficulty do
    throw (Err.invalidPow s.config.powDifficulty)
  let blobHash := p.file.hash
  unless verifyMessage p.senderPk (Msg.postConsignment p.transferId p.consignmentHash blobHash)
      p.signature do
    throw (Err.code Code.invalidContentSignature)
  let some inv := s.invoices.find? p.invoiceId | throw (Err.code Code.invoiceNotReserved)
  if s.deleted.contains p.transferId then throw (Err.code Code.transferIdDeleted)
  match s.transfers.find? p.transferId with
  | some t =>
    let changed := changedPostFields t p blobHash
    unless changed.isEmpty do throw (Err.cannotChange changed)
    return s
  | none =>
    if inv.expiresAt < s.now then throw (Err.code Code.invoiceExpired)
    if inv.quota ≤ inv.transfers.length then throw (Err.code Code.invoiceQuotaExceeded)
    let t : TransferRecord :=
      { invoiceId := p.invoiceId, senderTransportEndpoint := p.senderTransportEndpoint
        senderPk := p.senderPk, consignmentHash := p.consignmentHash, batch := p.batch
        blobHash, consignment := some p.file }
    return { s with
      transfers := s.transfers.insert p.transferId t
      invoices := s.invoices.insert p.invoiceId
        { inv with transfers := inv.transfers ++ [p.transferId] } }

/-- `consignment.get`: the posted consignment and its sender data; which of the codes the client
reads as no consignment answers which case is assumed. -/
def consignmentGet (s : Server) (transferId : String) :
    Except JsonRpcError ConsignmentGetResult :=
  match s.transfers.find? transferId with
  | none =>
    .error (Err.code (if s.deleted.contains transferId then Code.consignmentDeleted
      else Code.consignmentNotFound))
  | some t =>
    match t.consignment with
    | none => .error (Err.code Code.consignmentRetrieved)
    | some b =>
      .ok { consignment := b, senderTransportEndpoint := t.senderTransportEndpoint
            senderPk := t.senderPk, consignmentHash := t.consignmentHash, batch := t.batch }

/-- `media.post`: store a media of a posted transfer within the media limit; the sender's
signature, the answer for a missing transfer and the repeat that changes nothing are assumed. -/
def mediaPost (s : Server) (p : MediaPost) : Except JsonRpcError Server := do
  let some t := s.transfers.find? p.transferId | throw (Err.code Code.consignmentNotFound)
  if t.consignment.isNone then throw (Err.code Code.consignmentRetrieved)
  unless verifyMessage t.senderPk (Msg.postMedia p.transferId p.mediaId p.file.hash)
      p.signature do
    throw (Err.code Code.invalidContentSignature)
  match t.media.lookup p.mediaId with
  | some b =>
    if b != p.file then throw (Err.cannotChange ["file"])
    return s
  | none =>
    if s.config.maxMedia ≤ t.media.length then throw (Err.code Code.tooManyMedia)
    return { s with
      transfers := s.transfers.insert p.transferId
        { t with media := t.media ++ [(p.mediaId, p.file)] } }

/-- `media.get`: a media of a transfer whose data is still stored; any missing media is answered
alike (assumed). -/
def mediaGet (s : Server) (transferId mediaId : String) : Except JsonRpcError Blob :=
  let found := (s.transfers.find? transferId).bind fun t =>
    if t.consignment.isSome then t.media.lookup mediaId else none
  match found with
  | some b => .ok b
  | none => .error (Err.code Code.mediaNotFound)

/-- `transfer.list`: the transfers posted to an invoice and not deleted, in transfer id order. -/
def transferList (s : Server) (invoiceId : String) :
    Except JsonRpcError (List (String × TransferListStatus)) :=
  match s.invoices.find? invoiceId with
  | none => .error (Err.code Code.invoiceNotReserved)
  | some inv =>
    .ok ((OrdSet.ofList inv.transfers).toList.map fun tid =>
      let stored := ((s.transfers.find? tid).bind (·.consignment)).isSome
      (tid, if stored then .pending else .retrieved))

/-- `transfer.list` signed by the invoice's recipient key over a fresh timestamp (the code of a
bad signature is assumed, as for the other recipient calls). -/
def transferListAuth (s : Server) (invoiceId : String) (signature : Ed25519Sig) (timestamp : Nat) :
    Except JsonRpcError (List (String × TransferListStatus)) := do
  let some inv := s.invoices.find? invoiceId | throw (Err.code Code.invoiceNotReserved)
  unless s.fresh timestamp do throw (Err.invalid ["timestamp"])
  unless verifyMessage inv.recipientPk (Msg.listTransfers invoiceId (toString timestamp))
      signature do
    throw (Err.code Code.invalidEndpointAuth)
  transferList s invoiceId

/-- `transfer.retrieved`: delete a transfer's consignment and media; the transfer keeps its
quota slot and is listed as retrieved. A missing transfer is answered as such (assumed). -/
def transferRetrieved (s : Server) (transferId : String) : Except JsonRpcError Server :=
  match s.transfers.find? transferId with
  | none => .error (Err.code Code.consignmentNotFound)
  | some t =>
    .ok { s with
      transfers := s.transfers.insert transferId { t with consignment := none, media := [] } }

/-- `transfer.retrieved` signed by the invoice's recipient key. -/
def transferRetrievedAuth (s : Server) (transferId : String) (signature : Ed25519Sig) :
    Except JsonRpcError Server := do
  let some pk := s.recipientPkOf? transferId | throw (Err.code Code.consignmentNotFound)
  unless verifyMessage pk (Msg.transferRetrieved transferId) signature do
    throw (Err.code Code.invalidEndpointAuth)
  transferRetrieved s transferId

/-- `transfer.delete`: delete a transfer, freeing its quota slot; its id cannot be posted
again. Deleting it again changes nothing (assumed). -/
def transferDelete (s : Server) (transferId : String) : Except JsonRpcError Server :=
  match s.transfers.find? transferId with
  | none =>
    if s.deleted.contains transferId then .ok s else .error (Err.code Code.consignmentNotFound)
  | some t =>
    let invoices := match s.invoices.find? t.invoiceId with
      | some inv => s.invoices.insert t.invoiceId
          { inv with transfers := inv.transfers.erase transferId }
      | none => s.invoices
    .ok { s with transfers := s.transfers.erase transferId, invoices
                 deleted := s.deleted ++ [transferId] }

/-- `transfer.delete` signed by the invoice's recipient key. -/
def transferDeleteAuth (s : Server) (transferId : String) (signature : Ed25519Sig) :
    Except JsonRpcError Server := do
  if let some pk := s.recipientPkOf? transferId then
    unless verifyMessage pk (Msg.deleteTransfer transferId) signature do
      throw (Err.code Code.invalidEndpointAuth)
  transferDelete s transferId

/-- Whether an operation registers the same recipients and consignments as `data`. -/
def sameTransferData (op : OperationRecord) (data : OrdMap String AckTransferData) : Bool :=
  op.transfers.keys == data.keys && data.all fun tid d =>
    (op.transfers.find? tid).any fun r =>
      r.recipientPk == d.recipientPk && r.consignmentHash == d.consignmentHash

/-- Whether an operation holds the signed transactions of `data`; a cleared one differs. -/
def sameSignedTxs (op : OperationRecord) (data : OrdMap String AckTransferData) : Bool :=
  data.all fun tid d => (op.transfers.find? tid).all fun r => r.signedTx == some d.signedTx

/-- `ack.prepare`: register an operation with the signed transaction encrypted for each
recipient. After `ack.clean` the same data reports the cleared transaction as the only change,
and it stays cleared; otherwise the same data changes nothing (assumed). -/
def ackPrepare (s : Server) (p : AckPrepare) : Except JsonRpcError Server := do
  checkDraining s .ackPrepare
  checkProxyAuth s p.signature
    (Msg.prepareAckAuth p.senderPk (toString p.expiresAt) p.signedTxHash p.transferData)
  unless s.validExpiry p.expiresAt do throw (Err.invalid ["expires_at"])
  if p.transferData.isEmpty then throw (Err.missing ["transfer_data"])
  let data := OrdMap.ofList p.transferData
  match s.operations.find? p.senderPk with
  | some op =>
    let changed := changedFields [("expires_at", op.expiresAt != p.expiresAt),
      ("signed_tx_hash", op.signedTxHash != p.signedTxHash),
      ("transfer_data", !sameTransferData op data), ("signed_tx", !sameSignedTxs op data)]
    unless changed.isEmpty do throw (Err.cannotChange changed)
    return s
  | none =>
    if data.keys.any fun tid => (s.operationOf? [tid]).isSome then
      throw (Err.code Code.transferIdInUse)
    let transfers := data.mapValues fun d =>
      ({ recipientPk := d.recipientPk, consignmentHash := d.consignmentHash
         signedTx := some d.signedTx } : AckRecord)
    return { s with
      operations := s.operations.insert p.senderPk
        { senderPk := p.senderPk, expiresAt := p.expiresAt, signedTxHash := p.signedTxHash
          transfers } }

/-- `ack.post`: record a recipient's signed ACK or NACK, which cannot change. The last ACK
releases the signed transaction to every ACKed recipient, also past the expiration until the
data is deleted. An expired operation takes no other answer, not even a NACK (assumed). -/
def ackPost (s : Server) (transferId : String) (ack : Bool) (signature : Ed25519Sig) :
    Except JsonRpcError (Server × PostAckResponse) := do
  let some op := s.operationOf? [transferId] | throw (Err.code Code.operationNotFound)
  let some r := op.transfers.find? transferId | throw (Err.code Code.operationNotFound)
  unless verifyMessage r.recipientPk (Msg.ack transferId ack r.consignmentHash) signature do
    throw (Err.code Code.invalidContentSignature)
  if op.expiresAt < s.now then
    if op.released && ack && r.ack == some true then return (s, op.answer r)
    throw (Err.code Code.operationExpired)
  match r.ack with
  | some prev =>
    if prev != ack then throw (Err.cannotChange ["ack"])
    return (s, op.answer r)
  | none =>
    let r := { r with ack := some ack, signature := some signature }
    let op := { op with transfers := op.transfers.insert transferId r }
    let op := { op with
      released := op.transfers.all fun _ x => x.ack == some true && x.signedTx.isSome }
    return ({ s with operations := s.operations.insert op.senderPk op }, op.answer r)

/-- `ack.get`: the recorded answers to transfers of one operation, also once it expired. -/
def ackGet (s : Server) (transferIds : List String) : Except JsonRpcError AckGetResult := do
  let some op := s.operationOf? transferIds | throw (Err.code Code.operationNotFound)
  let answered := (OrdSet.ofList transferIds).toList.filterMap fun tid => do
    let r ← op.transfers.find? tid
    let a ← r.ack
    let sig ← r.signature
    return (tid, a, sig)
  return { acks := answered.map fun (tid, a, _) => (tid, a)
           signatures := answered.map fun (tid, _, sig) => (tid, sig) }

/-- `ack.get` signed by the operation's sender key over a fresh timestamp. -/
def ackGetAuth (s : Server) (transferIds : List String) (signature : Ed25519Sig)
    (timestamp : Nat) : Except JsonRpcError AckGetResult := do
  let some op := s.operationOf? transferIds | throw (Err.code Code.operationNotFound)
  unless s.fresh timestamp do throw (Err.invalid ["timestamp"])
  unless verifyMessage op.senderPk (Msg.getAck transferIds (toString timestamp)) signature do
    throw (Err.code Code.invalidEndpointAuth)
  ackGet s transferIds

/-- `ack.clean`: clear the signed transactions of an operation not yet released; the rest of the
operation stays. -/
def ackClean (s : Server) (transferIds : List String) : Except JsonRpcError Server := do
  let some op := s.operationOf? transferIds | throw (Err.code Code.operationNotFound)
  if op.released then throw (Err.code Code.txAlreadyReleased)
  return { s with
    operations := s.operations.insert op.senderPk
      { op with transfers := op.transfers.mapValues fun r => { r with signedTx := none } } }

/-- `ack.clean` signed by the operation's sender key. -/
def ackCleanAuth (s : Server) (transferIds : List String) (signature : Ed25519Sig) :
    Except JsonRpcError Server := do
  let some op := s.operationOf? transferIds | throw (Err.code Code.operationNotFound)
  unless verifyMessage op.senderPk (Msg.cleanAck transferIds) signature do
    throw (Err.code Code.invalidEndpointAuth)
  ackClean s transferIds

end Wire

/-! ## Server calls as the wallet sees them

Each call answers with the wallet error `mapProxyError` gives its JSON-RPC error. The calls
without a signature parameter answer the caller the proxy authenticates; their `…Auth` forms
check the signature first. -/

namespace Server

/-- `invoice.prepare`. -/
def invoicePrepare (s : Server) (invoiceId : String) (expiresAt : Nat) (recipientPk : String)
    (quota : Nat) (signature : Option Ed25519Sig := none) : Except Error Server :=
  (Wire.invoicePrepare s invoiceId expiresAt recipientPk quota signature).mapError mapProxyError

/-- `consignment.post`. -/
def consignmentPost (s : Server) (p : ConsignmentPost) : Except Error Server :=
  (Wire.consignmentPost s p).mapError mapProxyError

/-- `consignment.get`. -/
def consignmentGet (s : Server) (transferId : String) : Except Error ConsignmentGetResult :=
  (Wire.consignmentGet s transferId).mapError mapProxyError

/-- `media.post`. -/
def mediaPost (s : Server) (p : MediaPost) : Except Error Server :=
  (Wire.mediaPost s p).mapError mapProxyError

/-- `media.get`. -/
def mediaGet (s : Server) (transferId mediaId : String) : Except Error Blob :=
  (Wire.mediaGet s transferId mediaId).mapError mapProxyError

/-- `transfer.list`. -/
def transferList (s : Server) (invoiceId : String) :
    Except Error (List (String × TransferListStatus)) :=
  (Wire.transferList s invoiceId).mapError mapProxyError

/-- `transfer.list`, authenticated. -/
def transferListAuth (s : Server) (invoiceId : String) (signature : Ed25519Sig) (timestamp : Nat) :
    Except Error (List (String × TransferListStatus)) :=
  (Wire.transferListAuth s invoiceId signature timestamp).mapError mapProxyError

/-- `transfer.retrieved`. -/
def transferRetrieved (s : Server) (transferId : String) : Except Error Server :=
  (Wire.transferRetrieved s transferId).mapError mapProxyError

/-- `transfer.retrieved`, authenticated. -/
def transferRetrievedAuth (s : Server) (transferId : String) (signature : Ed25519Sig) :
    Except Error Server :=
  (Wire.transferRetrievedAuth s transferId signature).mapError mapProxyError

/-- `transfer.delete`. -/
def transferDelete (s : Server) (transferId : String) : Except Error Server :=
  (Wire.transferDelete s transferId).mapError mapProxyError

/-- `transfer.delete`, authenticated. -/
def transferDeleteAuth (s : Server) (transferId : String) (signature : Ed25519Sig) :
    Except Error Server :=
  (Wire.transferDeleteAuth s transferId signature).mapError mapProxyError

/-- `ack.prepare`. -/
def ackPrepare (s : Server) (p : AckPrepare) : Except Error Server :=
  (Wire.ackPrepare s p).mapError mapProxyError

/-- `ack.post`. -/
def ackPost (s : Server) (transferId : String) (ack : Bool) (signature : Ed25519Sig) :
    Except Error (Server × PostAckResponse) :=
  (Wire.ackPost s transferId ack signature).mapError mapProxyError

/-- `ack.get`. -/
def ackGet (s : Server) (transferIds : List String) : Except Error AckGetResult :=
  (Wire.ackGet s transferIds).mapError mapProxyError

/-- `ack.get`, authenticated. -/
def ackGetAuth (s : Server) (transferIds : List String) (signature : Ed25519Sig)
    (timestamp : Nat) : Except Error AckGetResult :=
  (Wire.ackGetAuth s transferIds signature timestamp).mapError mapProxyError

/-- `ack.clean`. -/
def ackClean (s : Server) (transferIds : List String) : Except Error Server :=
  (Wire.ackClean s transferIds).mapError mapProxyError

/-- `ack.clean`, authenticated. -/
def ackCleanAuth (s : Server) (transferIds : List String) (signature : Ed25519Sig) :
    Except Error Server :=
  (Wire.ackCleanAuth s transferIds signature).mapError mapProxyError

/-- `check_proxy` of this proxy. -/
def checkProxy (s : Server) : Except Error ServerInfo := Proxy.checkProxy s.serverInfo

/-- `post_consignment_with_pow`: post with no proof of work, then with the difficulty the proxy
asks for while it is at most `maxPowDifficulty`, `maxPowAttempts` times in all; the proof of
work is for `now`, the sender's clock. -/
def postConsignmentWithPow (s : Server) (p : ConsignmentPost) (now : Nat := s.now) :
    Except Error Server :=
  go maxPowAttempts 0
where
  /-- Post with `difficulty`, `attempts` times at most. -/
  go : Nat → Nat → Except Error Server
    | 0, _ => .error (.proxy "proof of work not accepted")
    | attempts + 1, difficulty =>
      let nonce := solvePow p.transferId (toString now) difficulty
      match Wire.consignmentPost s { p with powTimestamp := now, powNonce := nonce } with
      | .ok s => .ok s
      | .error e =>
        match powDifficultyRequired e with
        | some d => if d ≤ maxPowDifficulty then go attempts d else .error (mapProxyError e)
        | none => .error (mapProxyError e)

end Server

/-! ## Calls over the proxies of an invoice -/

/-- Reserve an invoice on its proxies in order, as a receive does: a proxy failing `check_proxy`
is skipped, a draining one noted, any other refusal returned; with no reservation the receive
fails as draining if a proxy was. Gives the proxies and the latest `expiresAt` plus grace. -/
def reserveInvoice (proxies : List Server) (invoiceId : String) (expiresAt : Nat)
    (recipientPk : String) (quota : Nat) (authKeys : List (String × SecretKey) := []) :
    Except Error (List Server × Nat) := do
  let message := Msg.prepareInvoiceAuth invoiceId (toString expiresAt) recipientPk quota
  let mut out : List Server := []
  let mut deadline : Option Nat := none
  let mut draining := false
  for s in proxies do
    match s.checkProxy with
    | .error _ => out := out ++ [s]
    | .ok info =>
      let signature := (authKeys.lookup s.url).map (signMessage · message)
      match s.invoicePrepare invoiceId expiresAt recipientPk quota signature with
      | .ok s' =>
        out := out ++ [s']
        let d := expiresAt + proxyRetentionGrace info
        deadline := some (max d (deadline.getD d))
      | .error .proxyDraining =>
        draining := true
        out := out ++ [s]
      | .error e => throw e
  match deadline with
  | some d => return (out, d)
  | none => throw (if draining then .proxyDraining else .noValidTransportEndpoint)

/-- Whether an invoice can take a transfer, as a send checks it on the invoice's proxies: one
proxy answering available is enough; otherwise the invoice is full if a proxy says so, else not
reserved if a proxy says so, else no endpoint is valid. -/
def checkInvoiceAvailable (proxies : List Server) (invoiceId : String) : Except Error Unit :=
  let statuses := proxies.filterMap fun s => (s.invoiceCheck [invoiceId]).lookup invoiceId
  if statuses.contains .available then .ok ()
  else if statuses.contains .full then .error .invoiceQuotaExceeded
  else if statuses.contains .unknown then .error .invoiceNotReserved
  else .error .noValidTransportEndpoint

end Rgb.Lib.Proxy
