import Rgb.Lib.Vanilla

/-!
# The wallet's proxy client

How the wallet talks to the RGB proxies of its world (`api/proxy.rs` as `online.rs` uses it). A
proxy answers at its HTTP URL. A call to a URL nothing answers at fails with the transport error
(`Error::Proxy`), which the wallet tells apart from the proxy's JSON-RPC errors (mapped by
`mapProxyError`). Signed calls are signed over the wallet's clock, which the proxy accepts
within its tolerance of its own.

Steps that talk to the network run in `Net`. What a step does to the proxies, to the chain and
to the wallet's files (`World.files`) stays when the step fails afterwards, while the wallet
changes it returns are lost: rgb-lib rolls back its database transaction, not the calls it made
nor the files it wrote.
-/

namespace Rgb.Lib

open ProxyCrypto Proxy

/-- A wallet step that talks to the proxies and the chain of the world. -/
abbrev Net := ExceptT Error (StateM World)

namespace Net

/-- A wallet result as a step. -/
def ofResult {α : Type} : Result α → Net α
  | .ok a => pure a
  | .error e => throw e

/-- The step's result, as a value. -/
def attempt {α : Type} (x : Net α) : Net (Result α) :=
  tryCatch (Except.ok <$> x) fun e => pure (.error e)

/-- Run a step on a world: its result and the world after it. -/
def exec {α : Type} (x : Net α) (world : World) : Result α × World :=
  Id.run (StateT.run (ExceptT.run x) world)

/-- The wallet's clock. -/
def now : Net Nat := do return (← get).now

end Net

namespace ProxyClient

/-- The transport error of a call to a URL nothing answers at (`Error::Proxy` with the HTTP
client's text, which names the URL). -/
def unreachable (url : String) : Error := .proxy s!"error sending request for url ({url})"

/-- The proxy at `url`; the transport error when none answers there. -/
def proxyAt (url : String) : Net Server := do
  match (← get).proxies.lookup url with
  | some s => pure s
  | none => throw (unreachable url)

/-- Keep the state a proxy is in after a call. -/
def storeProxy (url : String) (s : Server) : Net Unit :=
  modify fun w => { w with proxies := w.proxies.map fun (u, x) => (u, if u == url then s else x) }

/-- `check_proxy(url)` in a world: the proxy's information, if it answers and speaks the
supported protocol. -/
def checkProxyIn (world : World) (url : String) : Result ServerInfo :=
  match world.proxies.lookup url with
  | some s => s.checkProxy
  | none => .error (unreachable url)

/-- `sender_proxy_retention_grace(url)`. -/
def senderRetentionGrace (url : String) : Net Nat := do
  Net.ofResult (senderProxyRetentionGrace (← proxyAt url).serverInfo)

/-- Signature of a call to the proxy at `url` with the wallet's authentication key for it, if one
is configured (`proxy_auth_signature`). -/
def authSignature (keys : List (String × SecretKey)) (url message : String) :
    Option Ed25519Sig :=
  (keys.lookup url).map (signMessage · message)

/-- `sign_and_post_ack`: the recipient's ACK or NACK, signed with its operation key. -/
def signAndPostAck (senderProxy transferId : String) (ack : Bool) (consignmentHash : String)
    (recipient : SecretKey) : Net PostAckResponse := do
  let s ← proxyAt senderProxy
  let signature := ackSignature recipient transferId ack consignmentHash
  let (s', res) ← Net.ofResult (s.ackPost transferId ack signature)
  storeProxy senderProxy s'
  return res

/-- `get_consignment`: every failure reads as no consignment. -/
def getConsignment (url transferId : String) : Net (Result ConsignmentGetResult) := do
  return match (← get).proxies.lookup url with
    | none => .error .noConsignment
    | some s => (s.consignmentGet transferId).mapError fun _ => .noConsignment

/-- `fetch_invoice_transfer`: the transfer, if it can be downloaded and was posted by the
sender its id derives from. -/
def fetchInvoiceTransfer (url invoiceId transferId : String) :
    Net (Option ConsignmentGetResult) := do
  match ← getConsignment url transferId with
  | .ok r => return if postedBySender invoiceId transferId r then some r else none
  | .error _ => return none

/-- `list_invoice_transfers`: `transfer.list`, signed by the recipient key over the wallet's
clock. -/
def listTransfers (url invoiceId : String) (recipient : SecretKey) :
    Net (Result (List (String × TransferListStatus))) := do
  let s ← proxyAt url
  let t ← Net.now
  let signature := signMessage recipient (Msg.listTransfers invoiceId (toString t))
  return s.transferListAuth invoiceId signature t

/-- `list_proxy_invoice_transfers`: the transfers to an invoice in id order, ignoring ids that
are not transfer ids; none when the proxy cannot list them. -/
def listInvoiceTransfers (url invoiceId : String) (recipient : SecretKey) :
    Net (Option (List (String × TransferListStatus))) := do
  match ← Net.attempt (listTransfers url invoiceId recipient) with
  | .ok (.ok l) =>
    return some ((l.filter (isTransferId ·.1)).mergeSort fun a b => compare a.1 b.1 != .gt)
  | _ => return none

/-- `find_invoice_transfer`: the first pending transfer to the invoice that can be fetched. -/
def findInvoiceTransfer (url invoiceId : String) (recipient : SecretKey) :
    Net (Option (String × ConsignmentGetResult)) := do
  let some listed ← listInvoiceTransfers url invoiceId recipient | return none
  for (tid, st) in listed do
    if st != .pending then continue
    if let some r ← fetchInvoiceTransfer url invoiceId tid then return some (tid, r)
  return none

/-- `release_transfer_data`: let the proxy delete a handled transfer's data
(`transfer.retrieved`), or the whole transfer, freeing its quota slot (`transfer.delete`); a
failure is only logged. -/
def releaseTransferData (url transferId : String) (recipient : SecretKey) (delete : Bool) :
    Net Unit := do
  let some s := (← get).proxies.lookup url | return
  let r := if delete then
      s.transferDeleteAuth transferId (signMessage recipient (Msg.deleteTransfer transferId))
    else
      s.transferRetrievedAuth transferId (signMessage recipient (Msg.transferRetrieved transferId))
  if let .ok s' := r then storeProxy url s'

/-- `get_ack_signed`: `ack.get`, signed by the operation key over the wallet's clock. -/
def getAck (url : String) (transferIds : List String) (sender : SecretKey) :
    Net (Result AckGetResult) := do
  let s ← proxyAt url
  let t ← Net.now
  return s.ackGetAuth transferIds (signMessage sender (Msg.getAck transferIds (toString t))) t

/-- `ack.clean` of `clean_sender_ack`, signed by the operation key: its mapped error, if any. -/
def cleanAck (url : String) (transferIds : List String) (sender : SecretKey) :
    Net (Option Error) := do
  let s ← proxyAt url
  match s.ackCleanAuth transferIds (signMessage sender (Msg.cleanAck transferIds)) with
  | .ok s' => storeProxy url s'; return none
  | .error e => return some e

/-- A signature as the wallet stores it (`ack_signature`): the model's signature in hex. -/
def sigHex (s : Ed25519Sig) : String := s.signer ++ s.digest

/-- `proxy_seal_blinding`: the witness seal blinding both parties derive, if the sender key is
a public key. -/
def sealBlinding (recipient : SecretKey) (senderPk : String) : Option UInt64 :=
  if isPubkeyHex senderPk then some (deriveShared recipient senderPk).sealBlinding else none

/-- `broadcast_deadline`: the operation expiration of an `ack.post` answer plus the retention
grace; none when the expiration is unreadable, past, or after the invoice expiration. -/
def broadcastDeadline (expiresAt : Option String) (grace : Nat) (invoiceExpiration : Option Nat)
    (now : Nat) : Option Nat := do
  let e ← expiresAt.bind parseI64?
  let inv ← invoiceExpiration
  if e < now ∨ e > inv then none else some (e.toNat + grace)

end ProxyClient

/-- `broadcast_tx`: a transaction the chain refuses counts as broadcast when the chain knows it
already. -/
def broadcastTx (tx : Tx) : Net Unit := do
  let c := (← get).chain
  match c.broadcast tx with
  | .ok c' => modify fun w => { w with chain := c' }
  | .error e => if (c.findTx? tx.txid).isNone then throw (broadcastError e)

end Rgb.Lib
