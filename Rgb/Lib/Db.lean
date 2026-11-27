import Rgb.Lib.Objects
import Rgb.Lib.Error

/-!
# The wallet database

The tables rgb-lib keeps next to the stash (SQLite through SeaORM). Rows are
identified by an increasing index. A *batch transfer* is one operation (one
Bitcoin transaction), an *asset transfer* is the part of it about one asset, a
*transfer* is one recipient or one receive, and a *coloring* puts one allocation
on (or takes it off) a colored output (`txo`).
-/

namespace Rgb.Lib

/-- A colored-keychain output (`txo`). -/
structure DbTxo where
  idx : Nat
  outpoint : Outpoint
  btcAmount : Nat
  /-- Spent by a transaction this wallet broadcast. -/
  spent : Bool := false
  /-- The transaction is known (false for own outputs registered before broadcast). -/
  exists_ : Bool := true
  /-- Output of a witness receive not settled yet. -/
  pendingWitness : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- One operation: one transaction, its status and deadlines (`batch_transfer`). -/
structure DbBatchTransfer where
  idx : Nat
  txid : Option Txid := none
  status : TransferStatus
  createdAt : Nat
  updatedAt : Nat
  expiration : Option Nat := none
  minConfirmations : Nat := 1
  incoming : Bool
  /-- Seed of the per-operation Ed25519 key (none: a legacy transfer, or an operation with no
  counterparty). -/
  operationSecretKey : Option String := none
  /-- Until when the signed transaction may be broadcast: the operation expiration plus the
  sender proxy retention grace. -/
  broadcastDeadline : Option Nat := none
  /-- Blind receive reserved on proxies: the invoice expiration plus their longest retention
  grace, until which a transfer to it can still be downloaded. -/
  retentionDeadline : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- The part of an operation about one asset (`asset_transfer`). -/
structure DbAssetTransfer where
  idx : Nat
  /-- False for allocations moved along as a side effect. -/
  userDriven : Bool := true
  batchTransferIdx : Nat
  assetId : Option String
  transitionType : Option TypeOfTransition := none
  deriving DecidableEq, Repr, Inhabited

/-- One recipient of a send or one receive (`transfer`). -/
structure DbTransfer where
  idx : Nat
  assetTransferIdx : Nat
  requestedAssignment : Option Assignment := none
  recipientType : Option RecipientTypeFull := none
  recipientId : Option String := none
  ack : Option Bool := none
  invoiceString : Option String := none
  /-- Hex public key of the recipient's operation key; none for an out-of-band recipient. -/
  recipientPubkey : Option String := none
  /-- Hex SHA-256 of the plaintext consignment file. -/
  consignmentHash : Option String := none
  recipientEncryption : Encryption := .unsupported
  /-- The recipient's signature of its answer, as the sender proxy served it (hex). -/
  ackSignature : Option String := none
  /-- Id of the transfer on the proxies. -/
  proxyTransferId : Option String := none
  invoiceExpiration : Option Nat := none
  /-- The reusable invoice the receive belongs to. -/
  invoiceIdx : Option Nat := none
  /-- Data directory of a receive sharing its recipient id with others (`receive_dir`). -/
  receiveDir : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- One allocation put on or taken off a TXO (`coloring`). -/
structure DbColoring where
  idx : Nat
  txoIdx : Nat
  assetTransferIdx : Nat
  type : ColoringType
  assignment : Assignment
  deriving DecidableEq, Repr, Inhabited

/-- An asset the wallet knows (`asset`). -/
structure DbAsset where
  idx : Nat
  id : String
  schema : AssetSchema
  addedAt : Nat
  name : String
  ticker : Option String
  details : Option String
  precision : Nat
  initialSupply : Nat
  maxSupply : Option Nat := none
  knownCirculatingSupply : Option Nat := none
  timestamp : Int
  rejectList : Option RejectListLocation := none
  bridgeLocation : Option BridgeLocation := none
  linkedFromContract : Option String := none
  linkedToContract : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- A transport endpoint used by a transfer, with its role. -/
structure DbTransferEndpoint where
  transferIdx : Nat
  /-- The proxy's HTTP URL. -/
  endpoint : String
  kind : TransportEndpointKind
  /-- The recipient proxy the consignment went through. -/
  used : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A vanilla transaction begun or ended (`wallet_transaction`). -/
structure DbWalletTransaction where
  idx : Nat
  txid : Txid
  type : WalletTransactionType
  deriving DecidableEq, Repr, Inhabited

/-- An input reserved by a pending vanilla or colored operation (`reserved_txo`). -/
structure DbReservedTxo where
  outpoint : Outpoint
  forVanilla : Option Nat := none
  forColored : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- A reusable invoice: how many payments it takes and until when (`invoice`). -/
structure DbInvoice where
  idx : Nat
  quota : Nat
  assetId : Option String
  /-- The latest proxy retention deadline plus the clock skew margin: before it the invoice is
  live and its proxies are asked for the transfers to it. -/
  deadline : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `DbInvoice::live`: the invoice can still receive transfers. -/
def DbInvoice.live (i : DbInvoice) (now : Nat) : Bool := now < i.deadline

namespace DbBatchTransfer

/-- Without an operation key: a legacy transfer, which the proxy protocol 1.0 cannot complete
(`is_legacy`). -/
def isLegacy (b : DbBatchTransfer) : Bool := b.operationSecretKey.isNone

/-- `is_expired`: the expiration has passed. -/
def isExpired (b : DbBatchTransfer) (now : Nat) : Bool := b.expiration.any (· < now)

/-- `is_expired_with_margin`: the expiration has passed by more than `margin`. -/
def isExpiredWithMargin (b : DbBatchTransfer) (now margin : Nat) : Bool :=
  b.expiration.any (· + margin < now)

/-- `expired_beyond_skew_margin`: expired on a proxy clock up to the margin behind too. -/
def expiredBeyondSkewMargin (b : DbBatchTransfer) (now : Nat) : Bool :=
  b.isExpiredWithMargin now proxyClockSkewMarginSecs

/-- `broadcast_deadline_passed_beyond_skew_margin`: the broadcast deadline (or the expiration)
plus the clock skew margin has passed. -/
def broadcastDeadlinePassed (b : DbBatchTransfer) (now : Nat) : Bool :=
  (b.broadcastDeadline <|> b.expiration).any (· + proxyClockSkewMarginSecs < now)

/-- `confirmation_deadline_passed`: the broadcast deadline plus the confirmation margin has
passed; never without a broadcast deadline. -/
def confirmationDeadlinePassed (b : DbBatchTransfer) (now : Nat) : Bool :=
  b.broadcastDeadline.any (· + confirmationMarginSecs < now)

/-- `incoming_expired`: an incoming transfer that may be failed. One waiting for a released
transaction waits for its confirmation deadline; a blind receive reserved on proxies waits for
the expiration on the proxies' clocks too. -/
def incomingExpired (b : DbBatchTransfer) (now : Nat) : Bool :=
  if b.status == .waitingBroadcast && b.broadcastDeadline.isSome then
    b.confirmationDeadlinePassed now
  else if b.status == .waitingCounterparty && b.retentionDeadline.isSome then
    b.isExpiredWithMargin now proxyClockSkewMarginSecs
  else b.isExpired now

end DbBatchTransfer

/-- The `backup_info` row: unix nanosecond times of the last backup and of the last
operation, and, for multisig wallets, the index of the last hub operation processed. -/
structure DbBackupInfo where
  /-- Row index; the table holds a single row. -/
  idx : Nat := 1
  lastBackupTimestamp : Nat := 0
  lastOperationTimestamp : Nat := 0
  lastProcessedOperationIdx : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

structure Db where
  next : Nat := 1
  txos : List DbTxo := []
  batchTransfers : List DbBatchTransfer := []
  assetTransfers : List DbAssetTransfer := []
  transfers : List DbTransfer := []
  colorings : List DbColoring := []
  assets : List DbAsset := []
  endpoints : List DbTransferEndpoint := []
  walletTransactions : List DbWalletTransaction := []
  reserved : List DbReservedTxo := []
  invoices : List DbInvoice := []
  pendingWitnessScripts : List Script := []
  backupInfo : DbBackupInfo := {}
  deriving Repr, Inhabited

namespace Db

/-- A fresh row index. -/
def fresh (d : Db) : Nat × Db := (d.next, { d with next := d.next + 1 })

def txo? (d : Db) (o : Outpoint) : Option DbTxo := d.txos.find? (·.outpoint == o)
def txoByIdx? (d : Db) (i : Nat) : Option DbTxo := d.txos.find? (·.idx == i)
def batch? (d : Db) (i : Nat) : Option DbBatchTransfer := d.batchTransfers.find? (·.idx == i)
def batchByTxid? (d : Db) (t : Txid) (incoming : Bool) : Option DbBatchTransfer :=
  d.batchTransfers.find? fun b => b.txid == some t && b.incoming == incoming
def asset? (d : Db) (id : String) : Option DbAsset := d.assets.find? (·.id == id)
def assetTransfersOf (d : Db) (batch : Nat) : List DbAssetTransfer :=
  d.assetTransfers.filter (·.batchTransferIdx == batch)
def transfersOf (d : Db) (at_ : Nat) : List DbTransfer := d.transfers.filter (·.assetTransferIdx == at_)
def coloringsOf (d : Db) (at_ : Nat) : List DbColoring := d.colorings.filter (·.assetTransferIdx == at_)
def batchOfAssetTransfer? (d : Db) (at_ : Nat) : Option DbBatchTransfer :=
  (d.assetTransfers.find? (·.idx == at_)).bind fun a => d.batch? a.batchTransferIdx

/-- Insert or update a TXO: `exists` only turns true, an amount only replaces zero. -/
def setTxo (d : Db) (o : Outpoint) (amount : Nat) (exists_ : Bool := true) (pendingWitness : Bool := false) :
    Nat × Db :=
  match d.txo? o with
  | some t =>
    let t' := { t with exists_ := t.exists_ || exists_, btcAmount := if amount != 0 then amount else t.btcAmount }
    (t.idx, { d with txos := d.txos.map fun x => if x.idx == t.idx then t' else x })
  | none =>
    let (i, d) := d.fresh
    (i, { d with txos := d.txos ++ [⟨i, o, amount, false, exists_, pendingWitness⟩] })

def updateBatch (d : Db) (i : Nat) (f : DbBatchTransfer → DbBatchTransfer) : Db :=
  { d with batchTransfers := d.batchTransfers.map fun b => if b.idx == i then f b else b }

def updateTransfer (d : Db) (i : Nat) (f : DbTransfer → DbTransfer) : Db :=
  { d with transfers := d.transfers.map fun t => if t.idx == i then f t else t }

/-- Allocations on a TXO (`get_utxo_allocations`). -/
def allocationsOn (d : Db) (t : DbTxo) : List LocalRgbAllocation :=
  (d.colorings.filter (·.txoIdx == t.idx)).filterMap fun c =>
    (d.assetTransfers.find? (·.idx == c.assetTransferIdx)).bind fun at_ =>
      (d.batch? at_.batchTransferIdx).map fun b =>
        ⟨at_.assetId, c.assignment, b.status, c.type.isIncoming, t.spent⟩

/-- Unpaid blind invoices on a UTXO (`unpaid_invoices`): blind receives waiting for their
counterparty with no colorings yet. -/
def unpaidInvoices (d : Db) (o : Outpoint) : List DbTransfer :=
  d.transfers.filter fun tr =>
    tr.recipientType == some (.blind o) &&
    (d.batchOfAssetTransfer? tr.assetTransferIdx).any (fun b => b.incoming && b.status == .waitingCounterparty) &&
    (d.coloringsOf tr.assetTransferIdx).isEmpty

/-- Slots the live reusable blind invoices on a UTXO keep for the transfers they can still
receive: the quota less the transfers that did not fail. Without a clock every reusable invoice
counts as live. -/
def invoiceSlots (d : Db) (o : Outpoint) (now : Option Nat) : Nat :=
  let live := d.invoices.filter fun inv => now.all inv.live
  live.foldl (fun acc inv =>
    let ts := d.transfers.filter (·.invoiceIdx == some inv.idx)
    match ts.head?.bind (·.recipientType) with
    | some (.blind u) =>
      if u != o then acc else
      let received := (ts.filter fun t =>
        (d.batchOfAssetTransfer? t.assetTransferIdx).any (·.status != .failed)).length
      acc + (inv.quota - received)
    | _ => acc) 0

/-- Unpaid blind receives on a UTXO (`pending_blinded`), with the slots of live reusable
invoices. -/
def pendingBlinded (d : Db) (t : DbTxo) (now : Option Nat := none) : Nat :=
  (d.unpaidInvoices t.outpoint).length + d.invoiceSlots t.outpoint now

/-- Transport endpoints of a transfer. -/
def endpointsOf (d : Db) (ti : Nat) : List DbTransferEndpoint :=
  d.endpoints.filter (·.transferIdx == ti)

/-- Recipient proxy endpoints of a transfer, in their order. -/
def recipientProxiesOf (d : Db) (ti : Nat) : List DbTransferEndpoint :=
  (d.endpointsOf ti).filter (·.kind == .recipientProxy)

/-- The sender proxy URL of a transfer, if it has one. -/
def senderProxyOf? (d : Db) (ti : Nat) : Option String :=
  ((d.endpointsOf ti).find? (·.kind == .senderProxy)).map (·.endpoint)

/-- Set the `used` flag of a recipient proxy endpoint of a transfer. -/
def setEndpointUsed (d : Db) (ti : Nat) (url : String) (used : Bool) : Db :=
  { d with endpoints := d.endpoints.map fun e =>
      if e.transferIdx == ti && e.endpoint == url && e.kind == .recipientProxy then { e with used }
      else e }

/-- Save the sender proxy endpoint of a transfer, once (`save_sender_transport_endpoint`). -/
def saveSenderProxy (d : Db) (ti : Nat) (url : String) : Db :=
  if (d.senderProxyOf? ti).isSome then d
  else { d with endpoints := d.endpoints ++ [⟨ti, url, .senderProxy, false⟩] }

/-- Without recipient proxy endpoints a receive exchanges its consignment out of band
(`uses_out_of_band_exchange`: its invoice names no transport). -/
def usesOutOfBand (d : Db) (t : DbTransfer) : Bool := (d.recipientProxiesOf t.idx).isEmpty

/-- Every transfer of a batch (`get_batch_transfer_transfers`). -/
def transfersOfBatch (d : Db) (bi : Nat) : List DbTransfer :=
  (d.assetTransfersOf bi).flatMap fun a => d.transfersOf a.idx

/-- The asset transfer and transfer of an incoming batch (`get_incoming_transfer`). -/
def incomingTransfer? (d : Db) (bi : Nat) : Option (DbAssetTransfer × DbTransfer) := do
  let at_ ← (d.assetTransfersOf bi).head?
  let t ← (d.transfersOf at_.idx).head?
  return (at_, t)

/-- Outpoints reserved by pending colored operations. -/
def reservedColored (d : Db) : List Outpoint := (d.reserved.filter (·.forColored.isSome)).map (·.outpoint)
def reservedVanilla (d : Db) : List Outpoint := (d.reserved.filter (·.forVanilla.isSome)).map (·.outpoint)

end Db

end Rgb.Lib
