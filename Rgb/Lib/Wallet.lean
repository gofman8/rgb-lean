import Rgb.Lib.Db
import Rgb.Ops.Stock
import Rgb.Schemas.Standard

/-!
# The rgb-lib wallet

A wallet owns two keychains: the *colored* keychain, whose outputs may hold RGB
allocations (each known output is a `txo` row), and the *vanilla* keychain, which
holds bitcoin only. The wallet keeps the database of operations and the stash.
It must be the only instance using its keys: the UTXO set is checked against the
chain when going online.

The world the wallet acts in is a simulated chain and a clock. Addresses are
deterministic scripts derived from the master fingerprint, keychain and index.
-/

namespace Rgb.Lib

/-- What online operations act on: the chain and the time. -/
structure World where
  chain : Chain
  now : Nat
  deriving Repr, Inhabited

/-- The handle `go_online` returns; it must match the wallet's online session. -/
structure Online where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An outgoing operation prepared by a `_begin` (the `transfers/<txid>` directory). -/
structure PendingOp where
  txid : Txid
  /-- Unsigned witness transaction (the PSBT). -/
  tx : Tx
  /-- Present for RGB operations. -/
  fascia : Option Fascia := none
  kind : Option TypeOfTransition := none
  donation : Bool := false
  minConfirmations : Nat := 1
  expiration : Option Nat := none
  /-- Consignment per asset, written at `_end`. -/
  consignments : List (String × Consignment) := []
  deriving Repr, Inhabited

/-- A consignment received for a pending receive (`rcv_compose.rgb`). -/
structure Received where
  batchIdx : Nat
  consignment : Consignment
  deriving Repr, Inhabited

structure Wallet where
  data : WalletData
  keys : SinglesigKeys
  db : Db := {}
  stock : Stock := {}
  coloredNext : Nat := 0
  vanillaNext : Nat := 0
  onlineId : Option Nat := none
  pending : List PendingOp := []
  inbox : List Received := []
  deriving Repr, Inhabited

/-- Standard schema rules of an rgb-lib schema. -/
def AssetSchema.rules : AssetSchema → SchemaRules
  | .nia => Schemas.niaRules | .uda => Schemas.udaRules | .cfa => Schemas.cfaRules
  | .ifa => Schemas.ifaRules | .bfa => Schemas.bfaRules

namespace Wallet

def fingerprint (w : Wallet) : String := w.keys.masterFingerprint

/-! ## Keychains and addresses -/

def script (w : Wallet) (keychain : String) (i : Nat) : Script :=
  match w.keys.witnessVersion with
  | .taproot => .p2tr (Digest.of "address" [encode w.fingerprint, encode keychain, encode i])
  | .segwitV0 => .p2wpkh s!"{w.fingerprint}/{keychain}/{i}"

def coloredScript (w : Wallet) (i : Nat) : Script := w.script "colored" i
def vanillaScript (w : Wallet) (i : Nat) : Script := w.script "vanilla" i

/-- Stop gap of a full scan. -/
def stopGap : Nat := 20

def isColored (w : Wallet) (s : Script) : Bool :=
  (List.range (w.coloredNext + stopGap)).any fun i => w.coloredScript i == s

def isVanilla (w : Wallet) (s : Script) : Bool :=
  (List.range (w.vanillaNext + stopGap)).any fun i => w.vanillaScript i == s

/-- A new colored address, or colored #0 when colored reuse is on (`get_output_address`). -/
def coloredOutputAddress (w : Wallet) : Script × Wallet :=
  if w.data.addressReuseColoredAuto then (w.coloredScript 0, { w with coloredNext := max w.coloredNext 1 })
  else (w.coloredScript w.coloredNext, { w with coloredNext := w.coloredNext + 1 })

/-- A new colored address, never #0 when colored reuse is on (witness receives). -/
def newColoredAddress (w : Wallet) : Script × Wallet :=
  let w := if w.data.addressReuseColoredAuto then { w with coloredNext := max w.coloredNext 1 } else w
  (w.coloredScript w.coloredNext, { w with coloredNext := w.coloredNext + 1 })

/-- A vanilla address: #0 with vanilla reuse, else the next one (`get_address`). -/
def getAddress (w : Wallet) : Script × Wallet :=
  if w.data.addressReuseVanilla then (w.vanillaScript 0, { w with vanillaNext := max w.vanillaNext 1 })
  else (w.vanillaScript w.vanillaNext, { w with vanillaNext := w.vanillaNext + 1 })

/-! ## Creation and going online -/

/-- Create a wallet (`Wallet::new`): a positive allocation cap, at least one
schema, and no IFA/BFA on mainnet unless reckless schemas are allowed. The stash
imports the supported schemas. -/
def create (data : WalletData) (keys : SinglesigKeys) : Result Wallet := do
  if data.maxAllocationsPerUtxo == 0 then throw .noMaxAllocationsPerUtxo
  if data.supportedSchemas.isEmpty then throw .noSupportedSchemas
  if data.bitcoinNetwork == .mainnet && !data.allowRecklessSchemas then
    if let some s := data.supportedSchemas.find? (!·.allowedOnMainnet) then
      throw (.cannotUseSchemaOnMainnet s)
  let stock := data.supportedSchemas.foldl (fun st s => st.importSchema s.rules) ({} : Stock)
  return { data, keys, stock }

def chainNet (w : Wallet) : ChainNet := w.data.bitcoinNetwork.chainNet

/-- An `Online` handle must be this wallet's current session (`check_online`). -/
def checkOnline (w : Wallet) (o : Online) : Result Unit :=
  match w.onlineId with
  | none => .error .offline
  | some id => if id == o.id then .ok () else .error .cannotChangeOnline

/-- Register colored outputs the chain shows (`sync` of the colored keychain). -/
def sync (w : Wallet) (c : Chain) : Wallet :=
  let outs := c.allTxs.flatMap fun tx => tx.outputs.zipIdx.filterMap fun (o, i) =>
    if w.isColored o.script then some (tx.outpoint i, o.value.toNat) else none
  let db := outs.foldl (fun db (op, v) =>
    let known := db.txos.any fun t => t.outpoint == op && t.exists_
    if known then db else (db.setTxo op v).2) w.db
  { w with db }

/-- Unspent vanilla outputs, as the BDK view of the chain shows them. -/
def vanillaUtxos (w : Wallet) (c : Chain) : List (Outpoint × Nat) :=
  c.allTxs.flatMap fun tx => tx.outputs.zipIdx.filterMap fun (o, i) =>
    let op := tx.outpoint i
    if w.isVanilla o.script && c.isUnspent op then some (op, o.value.toNat) else none

/-- Go online (`go_online`): the session is set first; then the UTXOs the
database thinks unspent must be unspent on chain, or spent by this wallet's
own outgoing transfer waiting for its counterparty. -/
def goOnline (w : Wallet) (world : World) (skipConsistencyCheck : Bool := false) :
    Wallet × Online × Result Unit :=
  let w := { (w.sync world.chain) with onlineId := some world.now }
  let o : Online := ⟨world.now⟩
  if skipConsistencyCheck then (w, o, .ok ()) else
  let ownWaiting := w.db.batchTransfers.filter fun b => !b.incoming && b.status == .waitingCounterparty
  let spentByOwn (op : Outpoint) : Bool := ownWaiting.any fun b =>
    b.txid.any fun t => (w.pending.find? (·.txid == t)).any (·.tx.spends op)
  let diff := w.db.txos.filter fun t =>
    !t.spent && t.exists_ && !world.chain.isUnspent t.outpoint && !spentByOwn t.outpoint
  (w, o, if diff.isEmpty then .ok ()
    else .error (.inconsistency s!"spent bitcoins with another wallet: {diff.map (·.outpoint)}"))

/-! ## Allocations and slots -/

/-- Effective allocation cap of a UTXO. -/
def maxUtxoAllocations (w : Wallet) : Nat := w.data.allocationCap

/-- Unspent TXOs with their allocations and unpaid blind receives. -/
def unspents (w : Wallet) : List (DbTxo × List LocalRgbAllocation × Nat) :=
  (w.db.txos.filter (!·.spent)).map fun t => (t, w.db.allocationsOn t, w.db.pendingBlinded t)

/-- UTXOs that can take new allocations (`get_available_allocations`): existing,
not pending a witness receive, not excluded, at most `max` allocations and unpaid
receives (default: room for one more), and not being spent by a pending send. -/
def availableAllocations (w : Wallet) (exclude : List Outpoint) (max? : Option Nat := none) :
    List (DbTxo × List LocalRgbAllocation × Nat) :=
  let max := max?.getD (w.maxUtxoAllocations - 1)
  (w.unspents.map fun (t, allocs, pb) => (t, allocs.filter (·.status != .failed), pb)).filter
    fun (t, allocs, pb) =>
      t.exists_ && !t.pendingWitness && !exclude.contains t.outpoint && allocs.length + pb ≤ max &&
      !(allocs.any fun a => !a.incoming && (a.status == .initiated || a.status == .waitingCounterparty))

/-- Pick a UTXO for a new allocation (`get_utxo`): fewest allocations first; a
receive prefers a UTXO with pending incoming state, an issuance one without. -/
def getUtxo (w : Wallet) (exclude : List Outpoint) (pendingOperation : Bool) (max? : Option Nat := none) :
    Result DbTxo :=
  let cands := (w.availableAllocations (exclude ++ w.db.reservedColored) max?).mergeSort
    fun a b => a.2.1.length + a.2.2 ≤ b.2.1.length + b.2.2
  match cands with
  | [] => .error .insufficientAllocationSlots
  | first :: _ =>
    if first.2.1.isEmpty || cands.length == 1 then .ok first.1
    else
      let pref := cands.find? fun (_, allocs, _) =>
        if pendingOperation then allocs.any LocalRgbAllocation.future else !(allocs.any LocalRgbAllocation.future)
      .ok ((pref.getD first).1)

/-! ## Balances -/

/-- Asset balance (`get_asset_balance`): settled, future and spendable, each
capped at `u64::MAX`. -/
def assetBalance (w : Wallet) (assetId : String) : Balance :=
  let all := w.db.txos.map fun t => (t, w.db.allocationsOn t, w.db.pendingBlinded t)
  let mine (a : LocalRgbAllocation) : Bool := a.assetId == some assetId
  let amt (a : LocalRgbAllocation) : Nat := a.assignment.mainAmount
  let allocs := all.flatMap fun (_, l, _) => l.filter mine
  let settled := (allocs.filter LocalRgbAllocation.settled |>.map amt).sum
  let pendingIn := (allocs.filter (fun a => !a.txoSpent && a.incoming && a.status.isPending) |>.map amt).sum
  let witnessPending := (w.db.transfers.filter fun t =>
      (match t.recipientType with | some (.witness _) => true | _ => false) &&
      (w.db.batchOfAssetTransfer? t.assetTransferIdx).any (fun b => b.incoming && b.status == .waitingConfirmations) &&
      (w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)).any (·.assetId == some assetId)).map
    fun t => (t.requestedAssignment.map Assignment.mainAmount).getD 0
  let pendingOut := (allocs.filter (fun a => !a.incoming && a.status.isPending) |>.map amt).sum
  let future := settled + pendingIn + witnessPending.sum - pendingOut
  let unspendableUtxo (t : DbTxo) (l : List LocalRgbAllocation) (pb : Nat) : Bool :=
    (!t.spent && ((l.any fun a => (!a.incoming && a.status != .failed) || (a.incoming && a.status.isPending)) || pb > 0)) ||
    (t.spent && l.any fun a => !a.incoming && a.status == .waitingConfirmations)
  let unspendable := (all.filter (fun (t, l, pb) => unspendableUtxo t l pb)).map fun (_, l, _) =>
    ((l.filter fun a => mine a && a.settled).map amt).sum
  let cap (n : Nat) : Nat := min n Bound.u64
  ⟨cap settled, cap future, cap (settled - unspendable.sum)⟩

/-- Bitcoin balance per keychain: settled = confirmed, future = all, spendable =
all minus outputs reserved by pending vanilla operations. -/
def btcBalance (w : Wallet) (c : Chain) : BtcBalance :=
  let conf (o : Outpoint) : Bool := c.confirmations o.txid > 0
  let van := w.vanillaUtxos c
  let reserved := w.db.reservedVanilla
  let col := (w.db.txos.filter fun t => !t.spent && c.isUnspent t.outpoint).map fun t => (t.outpoint, t.btcAmount)
  let bal (l : List (Outpoint × Nat)) (res : List Outpoint) : Balance :=
    ⟨((l.filter (conf ·.1)).map (·.2)).sum, (l.map (·.2)).sum,
     ((l.filter fun (o, _) => !res.contains o).map (·.2)).sum⟩
  ⟨bal van reserved, bal col []⟩

/-! ## Views -/

def asset? (w : Wallet) (id : String) : Result DbAsset :=
  match w.db.asset? id with
  | some a => .ok a
  | none => .error (.assetNotFound id)

/-- Unspent colored outputs with their allocations (`list_unspents`). -/
def listUnspents (w : Wallet) (settledOnly : Bool := false) : List Unspent :=
  w.unspents.map fun (t, allocs, pb) =>
    ⟨⟨t.outpoint, t.btcAmount, true, t.exists_⟩,
     (allocs.filter fun a => !settledOnly || a.settled).map fun a => ⟨a.assetId, a.assignment, a.settled⟩, pb⟩

/-- Kind of a transfer as `list_transfers` shows it. -/
def transferKind (w : Wallet) (t : DbTransfer) : TransferKind :=
  let at_ := w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)
  let b := at_.bind fun a => w.db.batch? a.batchTransferIdx
  match b, t.recipientType with
  | some b, some (.blind _) => if b.incoming then .receiveBlind else .send
  | some b, some (.witness _) => if b.incoming then .receiveWitness else .send
  | some b, none =>
    if b.incoming && t.recipientId.isNone then .issuance
    else match at_.bind (·.transitionType) with
      | some .inflate => .inflation
      | some .burn => .burn
      | some .link => .link
      | some .mint => .mint
      | _ => .send
  | none, _ => .send

/-- Status of every transfer of an asset, by batch index. -/
def transferStatuses (w : Wallet) (assetId : String) : List (Nat × TransferStatus × TransferKind) :=
  (w.db.transfers.filterMap fun t =>
    (w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)).bind fun a =>
      if a.assetId == some assetId && a.userDriven then
        (w.db.batch? a.batchTransferIdx).map fun b => (b.idx, b.status, w.transferKind t)
      else none)

end Wallet

end Rgb.Lib
