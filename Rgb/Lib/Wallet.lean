import Rgb.Lib.Db
import Rgb.Lib.Evm
import Rgb.Lib.Keys
import Rgb.Lib.SchemaMap
import Rgb.Lib.Proxy
import Rgb.Lib.Recipient
import Rgb.Invoice.Invoice
import Rgb.Ops.Stock

/-!
# The rgb-lib wallet

A wallet owns two keychains: the *colored* keychain, whose outputs may hold RGB
allocations (each known output is a `txo` row), and the *vanilla* keychain, which
holds bitcoin only. The wallet keeps the database of operations and the stash.
It must be the only instance using its keys: the UTXO set is checked against the
chain when going online.

The world the wallet acts in is a simulated chain, a clock, the EVM nodes at
their RPC URLs, the RGB proxies at their HTTP URLs and the files each wallet keeps
in its data directory. Addresses are deterministic scripts derived from the master
fingerprint, keychain and index.
-/

namespace Rgb.Lib

/-- What a recipient keeps with a consignment downloaded from a proxy
(`ReceivedConsignmentMeta`). -/
structure ReceivedInfo where
  /-- The recipient proxy it came from. -/
  proxyUrl : Option String
  transferId : Option String
  /-- HTTP URL of the sender proxy, where the ACK goes. -/
  senderTransportEndpoint : String
  senderPubkey : String
  consignmentHash : String
  batch : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A consignment downloaded from a recipient proxy and decrypted (`rcv_compose.rgb`), with what
is saved along with it. -/
structure Download where
  file : ProxyCrypto.Payload
  info : ReceivedInfo
  deriving DecidableEq, Repr, Inhabited

/-- Files a wallet keeps in its data directory: a failed step, whose database changes roll back,
leaves them. -/
structure WalletFiles where
  /-- Consignments downloaded from recipient proxies, by transfer index. -/
  downloads : List (Nat × Download) := []
  /-- Transactions released to the wallet as a recipient, by transfer index (`rcv_signed.tx`). -/
  releasedTxs : List (Nat × Tx) := []
  deriving Repr, Inhabited

/-- What online operations act on: the chain, the time, the EVM chain behind each RPC URL, the
RGB proxy behind each HTTP URL and the files of each wallet. -/
structure World where
  chain : Chain
  now : Nat
  evm : List (String × Evm.EvmLedger) := []
  /-- The proxy answering at each HTTP URL; a call to any other URL gets no answer. -/
  proxies : List (String × Proxy.Server) := []
  /-- The files of each wallet, by its data directory (its master fingerprint). -/
  files : List (String × WalletFiles) := []
  deriving Repr, Inhabited

/-- The node answering at each URL: the honest node of its ledger; nothing answers elsewhere. -/
def World.evmNet (w : World) : Evm.EvmNet := fun url =>
  match w.evm.lookup url with
  | some l => l.node
  | none => .unreachable

/-- Add a proxy, answering at its URL. -/
def World.withProxy (w : World) (s : Proxy.Server) : World :=
  { w with proxies := w.proxies ++ [(s.url, s)] }

/-- The files of the wallet whose data directory is `dir`. -/
def World.filesOf (w : World) (dir : String) : WalletFiles := (w.files.lookup dir).getD {}

/-- Replace the files of the wallet whose data directory is `dir`. -/
def World.setFiles (w : World) (dir : String) (f : WalletFiles) : World :=
  { w with files := (w.files.filter (·.1 != dir)) ++ [(dir, f)] }

/-- The world at time `t`, not before now: every proxy's clock moves with it. -/
def World.setTime (w : World) (t : Nat) : World :=
  { w with now := t, proxies := w.proxies.map fun (u, s) => (u, s.tick (t - s.now)) }

/-- The handle `go_online` returns; it must match the wallet's online session. -/
structure Online where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An outgoing operation prepared by a `_begin` (the `transfers/<txid>` directory with its
`transfer_data.txt`). -/
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
  /-- Recipients per asset, in asset id order. -/
  recipients : List (String × List LocalRecipient) := []
  /-- Where proxy recipients post their ACK (`rpc://` text, as given). -/
  senderTransportEndpoint : Option String := none
  /-- Seed of the operation key; none for an operation with no counterparty. -/
  operationSecretKey : Option String := none
  createdAt : Nat := 0
  /-- A mint: the bridge block its lock has to be included before. -/
  beforeBlock : Option Nat := none
  deriving Repr, Inhabited

/-- A consignment received for a pending receive, validated (`rcv_compose.valid.rgb`). -/
structure Received where
  batchIdx : Nat
  consignment : Consignment
  /-- Its validation status, kept with it until it is accepted. -/
  status : Status
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
  /-- EVM chains checked when going online (`evm_chains`). -/
  evmChains : List (Nat × Evm.EvmChain) := []
  /-- Proxy authentication keys of the online session, by proxy URL (`proxy_auth_keys`). -/
  proxyAuthKeys : List (String × ProxyCrypto.SecretKey) := []
  /-- Operation keys generated so far. -/
  operationKeys : Nat := 0
  /-- Mints this wallet checked as their recipient, by transfer index (`rcv_mint.json`). -/
  receivedMints : List (Nat × Evm.ReceivedMint) := []
  /-- Mint locks a received consignment waits for, by transfer index
  (`rcv_compose.mint_locks.json`). -/
  mintLocks : List (Nat × Evm.PendingMintLocks) := []
  /-- `accepts_received_mints`: this singlesig wallet does; a multisig wallet refuses mints. -/
  acceptsReceivedMints : Bool := true
  deriving Repr, Inhabited

namespace Wallet

def fingerprint (w : Wallet) : String := w.keys.masterFingerprint

/-! ## Keychains and addresses -/

def script (w : Wallet) (keychain : String) (i : Nat) : Script :=
  match w.keys.witnessVersion with
  | .taproot => .p2tr (Digest.of "address" [encode w.fingerprint, encode keychain, encode i])
  | .segwitV0 => .p2wpkh s!"{w.fingerprint}/{keychain}/{i}"

def coloredScript (w : Wallet) (i : Nat) : Script := w.script "colored" i
def vanillaScript (w : Wallet) (i : Nat) : Script := w.script "vanilla" i

def isColored (w : Wallet) (s : Script) : Bool :=
  (List.range (w.coloredNext + indexerStopGap)).any fun i => w.coloredScript i == s

def isVanilla (w : Wallet) (s : Script) : Bool :=
  (List.range (w.vanillaNext + indexerStopGap)).any fun i => w.vanillaScript i == s

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

/-- Create a wallet (`Wallet::new`): the key checks, a positive allocation cap, at
least one schema, and no IFA/BFA on mainnet unless reckless schemas are allowed. The
stash imports the supported schemas. -/
def create (data : WalletData) (keys : SinglesigKeys) : Result Wallet := do
  let _ ← keys.buildDescriptors data.bitcoinNetwork
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

/-- `parse_proxy_auth_keys`: each key under its endpoint's proxy URL. A seed must be hex of
32 bytes; two endpoints of one URL are refused. -/
def parseProxyAuthKeys (keys : List (String × String)) :
    Result (List (String × ProxyCrypto.SecretKey)) := do
  let mut out : List (String × ProxyCrypto.SecretKey) := []
  for (endpoint, seed) in keys do
    let url := (← TransportEndpoint.new endpoint).endpoint
    let some b := (Hex.toBytes? seed).filter (·.length == 32)
      | throw (.invalidProxyAuthKey
          s!"expected a hex-encoded 32-byte Ed25519 seed for endpoint {endpoint}")
    if out.any (·.1 == url) then
      throw (.duplicateProxyAuthKey
        s!"endpoint {endpoint} resolves to a proxy URL ({url}) already covered by another entry")
    out := out ++ [(url, ⟨Hex.ofBytes b⟩)]
  return out

/-- Go online (`go_online`): the proxy authentication keys, then the EVM chains are checked (a
failure leaves the wallet as it was); then the session is set; then the UTXOs the database
thinks unspent must be unspent on chain, or spent by this wallet's own outgoing transfer
waiting for its counterparty. After a failed consistency check the wallet is online. -/
def goOnline (w : Wallet) (world : World) (skipConsistencyCheck : Bool := false)
    (evmChains : List (Nat × Evm.EvmChain) := []) (proxyAuthKeys : List (String × String) := []) :
    Wallet × Online × Result Unit :=
  match parseProxyAuthKeys proxyAuthKeys with
  | .error e => (w, ⟨w.onlineId.getD 0⟩, .error e)
  | .ok keys =>
  match Evm.checkEvmChains world.evmNet (w.data.supportedSchemas.contains .bfa) evmChains with
  | .error e => (w, ⟨w.onlineId.getD 0⟩, .error e)
  | .ok chains =>
  let w := { (w.sync world.chain) with
    onlineId := some world.now, evmChains := chains, proxyAuthKeys := keys }
  let o : Online := ⟨world.now⟩
  if skipConsistencyCheck then (w, o, .ok ()) else
  let ownWaiting := w.db.batchTransfers.filter fun b => !b.incoming && b.status == .waitingCounterparty
  let spentByOwn (op : Outpoint) : Bool := ownWaiting.any fun b =>
    b.txid.any fun t => (w.pending.find? (·.txid == t)).any (·.tx.spends op)
  let diff := w.db.txos.filter fun t =>
    !t.spent && t.exists_ && !world.chain.isUnspent t.outpoint && !spentByOwn t.outpoint
  (w, o, if diff.isEmpty then .ok ()
    else .error (.inconsistency s!"spent bitcoins with another wallet: {diff.map (·.outpoint)}"))

/-- A fresh operation key (`gen_ed25519`); its seed names the wallet, the time and a counter. -/
def newOperationKey (w : Wallet) (now : Nat) : ProxyCrypto.SecretKey × Wallet :=
  (⟨s!"{w.fingerprint}/op/{now}/{w.operationKeys}"⟩,
    { w with operationKeys := w.operationKeys + 1 })

/-- EVM RPC URLs by chain id (`evm_rpc_urls`). -/
def evmRpcUrls (w : Wallet) : Evm.EvmRpcUrls := w.evmChains.map fun (id, c) => (id, c.rpcUrl)

/-- `update_backup_info`: an operation changed the wallet at `now`, so an older backup misses it. -/
def updateBackupInfo (w : Wallet) (now : Nat) : Wallet :=
  let info := { w.db.backupInfo with lastOperationTimestamp := now }
  { w with db := { w.db with backupInfo := info } }

/-! ## Allocations and slots -/

/-- Effective allocation cap of a UTXO. -/
def maxUtxoAllocations (w : Wallet) : Nat := w.data.allocationCap

/-- Unspent TXOs with their allocations and unpaid blind receives; `now` tells which reusable
invoices are live (without it every one is). -/
def unspents (w : Wallet) (now : Option Nat := none) :
    List (DbTxo × List LocalRgbAllocation × Nat) :=
  (w.db.txos.filter (!·.spent)).map fun t =>
    (t, w.db.allocationsOn t, w.db.pendingBlinded t now)

/-- UTXOs that can take new allocations (`get_available_allocations`): existing,
not pending a witness receive, not excluded, at most `max` allocations and unpaid
receives (default: room for one more), and not being spent by a pending send. -/
def availableAllocations (w : Wallet) (exclude : List Outpoint) (max? : Option Nat := none)
    (now : Option Nat := none) : List (DbTxo × List LocalRgbAllocation × Nat) :=
  let max := max?.getD (w.maxUtxoAllocations - 1)
  ((w.unspents now).map fun (t, allocs, pb) => (t, allocs.filter (·.status != .failed), pb)).filter
    fun (t, allocs, pb) =>
      t.exists_ && !t.pendingWitness && !exclude.contains t.outpoint && allocs.length + pb ≤ max &&
      !(allocs.any fun a => !a.incoming && (a.status == .initiated || a.status == .waitingCounterparty))

/-- Pick a UTXO for a new allocation (`get_utxo`): fewest allocations first; a
receive prefers a UTXO with pending incoming state, an issuance one without. -/
def getUtxo (w : Wallet) (exclude : List Outpoint) (pendingOperation : Bool)
    (max? : Option Nat := none) (now : Option Nat := none) : Result DbTxo :=
  let cands := (w.availableAllocations (exclude ++ w.db.reservedColored) max? now).mergeSort
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
def assetBalance (w : Wallet) (assetId : String) (now : Option Nat := none) : Balance :=
  let all := w.db.txos.map fun t => (t, w.db.allocationsOn t, w.db.pendingBlinded t now)
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
def listUnspents (w : Wallet) (settledOnly : Bool := false) (now : Option Nat := none) :
    List Unspent :=
  (w.unspents now).map fun (t, allocs, pb) =>
    ⟨⟨t.outpoint, t.btcAmount, true, t.exists_⟩,
     (allocs.filter fun a => !settledOnly || a.settled).map fun a => ⟨a.assetId, a.assignment, a.settled⟩, pb⟩

/-- Kind of a transfer as `list_transfers` shows it: an incoming one by its recipient type, an
outgoing one by the transition its operation recorded. -/
def transferKind (w : Wallet) (t : DbTransfer) : TransferKind :=
  let at_ := w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)
  match at_.bind fun a => w.db.batch? a.batchTransferIdx with
  | none => .send
  | some b =>
    if b.incoming then
      match t.recipientType with
      | some (.blind _) => .receiveBlind
      | some (.witness _) => .receiveWitness
      | none => if t.recipientId.isNone then .issuance else .send
    else match at_.bind (·.transitionType) with
      | some .inflate => .inflation
      | some .burn => .burn
      | some .link => .link
      | some .mint => .mint
      | _ => .send

/-- An asset as `list_assets` shows it, with its balance as of `now`. -/
def assetInfo (w : Wallet) (a : DbAsset) (now : Option Nat := none) : AssetInfo :=
  { assetId := a.id, schema := a.schema, ticker := a.ticker, name := a.name, details := a.details
    precision := a.precision, issuedSupply := a.initialSupply, maxSupply := a.maxSupply.getD a.initialSupply
    knownCirculatingSupply := a.knownCirculatingSupply.getD a.initialSupply, timestamp := a.timestamp
    addedAt := a.addedAt, balance := w.assetBalance a.id now, rejectList := a.rejectList
    bridgeLocation := a.bridgeLocation, linkedFromContract := a.linkedFromContract
    linkedToContract := a.linkedToContract }

/-- Assets of the requested schemas (all when none is given), in schema order (`list_assets`),
with their balances as of `now`. -/
def listAssets (w : Wallet) (schemas : List AssetSchema := []) (now : Option Nat := none) :
    List AssetInfo :=
  let ss := if schemas.isEmpty then AssetSchema.all else schemas
  ss.flatMap fun s => (w.db.assets.filter (·.schema == s)).map (w.assetInfo · now)

/-- Transfers of an asset as `list_transfers` shows them. -/
def listTransfers (w : Wallet) (assetId : Option String) : Result (List TransferView) := do
  if let some id := assetId then
    if (w.db.asset? id).isNone then throw (.assetNotFound id)
  return (w.db.transfers.filterMap fun t =>
    (w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)).bind fun a =>
      if a.assetId != assetId || !a.userDriven then none else
      (w.db.batch? a.batchTransferIdx).map fun b =>
        let colorings := w.db.coloringsOf a.idx
        { idx := t.idx, batchTransferIdx := b.idx, createdAt := b.createdAt, updatedAt := b.updatedAt
          status := b.status, requestedAssignment := t.requestedAssignment
          assignments := (colorings.filter (·.type != .input)).map (·.assignment)
          kind := w.transferKind t, txid := b.txid, recipientId := t.recipientId
          receiveUtxo := match t.recipientType with
            | some (.blind o) => some o
            | some (.witness (some v)) => b.txid.map (⟨·, v⟩)
            | _ => none
          changeUtxos := ((colorings.filter (·.type == .change)).filterMap fun c =>
            (w.db.txoByIdx? c.txoIdx).map (·.outpoint))
          expirationTimestamp := b.expiration })

/-- Status of every transfer of an asset, by batch index. -/
def transferStatuses (w : Wallet) (assetId : String) : List (Nat × TransferStatus × TransferKind) :=
  (w.db.transfers.filterMap fun t =>
    (w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)).bind fun a =>
      if a.assetId == some assetId && a.userDriven then
        (w.db.batch? a.batchTransferIdx).map fun b => (b.idx, b.status, w.transferKind t)
      else none)

end Wallet

end Rgb.Lib
