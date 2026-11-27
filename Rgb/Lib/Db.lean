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
  /-- Seed of the per-operation Ed25519 key (none: a legacy transfer). -/
  operationSecretKey : Option String := none
  broadcastDeadline : Option Nat := none
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
  recipientPubkey : Option String := none
  consignmentHash : Option String := none
  recipientEncryption : Encryption := .unsupported
  ackSignature : Option String := none
  proxyTransferId : Option String := none
  invoiceExpiration : Option Nat := none
  invoiceIdx : Option Nat := none
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
  endpoint : String
  kind : TransportEndpointKind
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
  deadline : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Last backup and last operation times (`backup_info`). -/
structure DbBackupInfo where
  lastBackup : Nat := 0
  lastOperation : Nat := 0
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

/-- Unpaid blind receives on a UTXO (`pending_blinded`). -/
def pendingBlinded (d : Db) (t : DbTxo) : Nat :=
  (d.transfers.filter fun tr =>
    tr.recipientType == some (.blind t.outpoint) &&
    (d.batchOfAssetTransfer? tr.assetTransferIdx).any (fun b => b.incoming && b.status == .waitingCounterparty) &&
    (d.coloringsOf tr.assetTransferIdx).isEmpty).length

/-- Outpoints reserved by pending colored operations. -/
def reservedColored (d : Db) : List Outpoint := (d.reserved.filter (·.forColored.isSome)).map (·.outpoint)
def reservedVanilla (d : Db) : List Outpoint := (d.reserved.filter (·.forVanilla.isSome)).map (·.outpoint)

end Db

end Rgb.Lib
