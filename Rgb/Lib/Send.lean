import Rgb.Lib.Receive

/-!
# Sending

`send_begin` checks the recipients, selects inputs, builds the witness
transaction (output 0 `OP_RETURN`, then one output per witness recipient, then
bitcoin change to a colored address) and colors it: per asset one transition
paying the recipients with the change back to the wallet, plus one transition
per other allocation that sits on a spent UTXO, or mint right the recipients do
not take, moving it to a change slot (state on a spent output that no transition
moves is lost). A change slot takes at most one mint right of an asset. The
bundles are committed in the `OP_RETURN` output. `send_end` takes the signed
transaction, builds one consignment per asset for the recipients, and either
broadcasts at once (donation) or waits for the recipients' ACK.

Each send gets a fresh operation key. A proxy recipient (one with transport
endpoints) names its proxies, the public key of its own operation key and its
invoice expiration. `send_begin` checks that a proxy answers for it and that its
invoice can take the transfer (`invoice.check`); a witness seal to it is blinded
with the blinding both keys derive. Unless it is a donation, `send_end` registers
the operation on the sender proxy (`ack.prepare`) with the signed transaction
encrypted for each proxy recipient, then posts each consignment, encrypted for its
recipient, to the first recipient proxy that takes it.

Model simplifications: all state of the asset on a selected UTXO is spent (not
only the part that covers the need); signing returns the unsigned transaction.
-/

namespace Rgb.Lib

namespace Wallet

/-- Operation expiration (`check_operation_expiration`): at least 300 s and at most ten years ahead. -/
def checkOperationExpiration (now e : Nat) : Result Unit :=
  if e < now + proxyClockSkewMarginSecs || e > now + maxExpirationSecs then .error .invalidExpiration
  else .ok ()

/-- Recipient checks (`parse_recipient`), in order. A proxy recipient's witness seal is blinded
with the blinding the operation key and the recipient's key derive; an out-of-band one takes the
given blinding or a fresh one. A mint recipient has no expiration: a mint expires by its lock. -/
def parseRecipient (w : Wallet) (now : Nat) (schema : AssetSchema) (r : Recipient) (vout i : Nat)
    (opKey : ProxyCrypto.SecretKey) (mint : Bool := false) : Result LocalRecipient := do
  if !schema.supportsAssignment r.assignment then throw .invalidAssignment
  if r.assignment == .fungible 0 || r.assignment == .inflationRight 0 then throw .invalidAmountZero
  let (net, b) ← Beneficiary.parse r.recipientId
  if net != w.chainNet then throw .invalidRecipientNetwork
  let (endpoints, publicKey, invoiceExpiration) ← (do
    if r.transportEndpoints.isEmpty then pure ([], none, none) else
    checkTransportEndpoints r.transportEndpoints
    let urls ← proxyUrls r.transportEndpoints
    let some pkHex := r.publicKey | throw (.invalidPubkey "missing recipient public key")
    let some pk := Hex.toBytes? pkHex
      | throw (.invalidPubkey "recipient public key is not valid hex")
    if pk.length != 32 then throw (.invalidPubkey "invalid Ed25519 public key length")
    let eps := urls.map ({ endpoint := · })
    if mint then
      if r.expirationTimestamp.isSome then
        throw (.invalidRecipientData "a mint recipient cannot have an expiration")
      return (eps, some (Hex.ofBytes pk), none)
    let some e := r.expirationTimestamp
      | throw (.invalidRecipientData "missing invoice expiration")
    if e ≤ now then throw .invoiceExpired
    if e > now + maxExpirationSecs then throw .invalidExpiration
    pure (eps, some (Hex.ofBytes pk), some e) :
    Result (List LocalTransportEndpoint × Option String × Option Nat))
  let lr : LocalRecipient := { recipientId := r.recipientId, beneficiary := b
                               assignment := r.assignment, endpoints, publicKey
                               encryption := r.encryption, invoiceExpiration }
  match b with
  | .blindedSeal _ =>
    if r.witnessData.isSome then
      throw (.invalidRecipientData "cannot provide witness data for a blinded recipient")
    return lr
  | .witnessVout _ =>
    let some wd := r.witnessData
      | throw (.invalidRecipientData "missing witness data for a witness recipient")
    let blinding ← match publicKey with
      | none => pure (wd.blinding.getD (now.toUInt64 * 31 + i.toUInt64))
      | some pk =>
        if wd.blinding.isSome then
          throw (.invalidRecipientData
            "cannot provide a blinding for a witness recipient with transport endpoints")
        pure (ProxyCrypto.deriveShared opKey pk).sealBlinding
    return { lr with vout := some vout, amountSat := wd.amountSat, blinding }

/-- The proxy URLs among the recipients' endpoints that answer `check_proxy`, each asked once. -/
def usableEndpoints (world : World) (lrs : List LocalRecipient) : List String :=
  ((lrs.flatMap (·.endpoints)).map (·.endpoint)).eraseDups.filter fun u =>
    (ProxyClient.checkProxyIn world u) matches .ok _

/-- Mark the recipient's endpoints among `usable` as usable. -/
def _root_.Rgb.Lib.LocalRecipient.markUsable (lr : LocalRecipient) (usable : List String) :
    LocalRecipient :=
  { lr with endpoints := lr.endpoints.map fun e => { e with usable := usable.contains e.endpoint } }

/-- The seal paying a recipient (`get_beneficiary_seal`): its concealed seal, or its witness
output with the recipient's blinding. -/
def _root_.Rgb.Lib.LocalRecipient.builderSeal (lr : LocalRecipient) : BuilderSeal GraphSeal :=
  match lr.beneficiary, lr.vout with
  | .blindedSeal sec, _ => .concealed sec
  | .witnessVout _, some v => .revealed (GraphSeal.witnessVout v.toUInt32 lr.blinding)
  | .witnessVout _, none => .concealed default

/-- `check_recipients_transport_endpoints`: a proxy recipient needs a usable endpoint. -/
def checkUsableEndpoints (lrs : List LocalRecipient) : Result Unit :=
  if lrs.any fun lr => !lr.endpoints.isEmpty && !lr.endpoints.any (·.usable) then
    .error (.invalidTransportEndpoints "no valid transport endpoints")
  else .ok ()

/-- UTXOs an RGB operation may spend (`get_input_unspents`). -/
def inputUnspents (w : Wallet) (now : Option Nat := none) :
    List (DbTxo × List LocalRgbAllocation) :=
  ((w.unspents now).filter fun (t, allocs, pb) =>
    t.exists_ && !t.pendingWitness && pb == 0 && !w.db.reservedColored.contains t.outpoint &&
    !(allocs.any fun a => a.incoming && a.status.isPending) &&
    !(allocs.any fun a => !a.incoming && (a.status == .initiated || a.status == .waitingCounterparty))).map
    fun (t, a, _) => (t, a)

/-- Select UTXOs holding settled state of the asset until the need is covered
(`select_rgb_inputs`); smaller holdings first. -/
def selectInputs (_w : Wallet) (assetId : String) (need : AssignmentsCollection)
    (cands : List (DbTxo × List LocalRgbAllocation)) : Result (List DbTxo) := do
  let held (l : List LocalRgbAllocation) := l.filter fun a => a.assetId == some assetId && a.settled
  let withAsset := (cands.filter fun (_, l) => !(held l).isEmpty).mergeSort fun a b =>
    (AssignmentsCollection.ofList ((held a.2).map (·.assignment))).fungible ≤
      (AssignmentsCollection.ofList ((held b.2).map (·.assignment))).fungible
  let mut picked : List DbTxo := []
  let mut got : AssignmentsCollection := {}
  for (t, l) in withAsset do
    if got.enough need then break
    let has := AssignmentsCollection.ofList ((held l).map (·.assignment))
    let useful := (need.fungible > got.fungible && has.fungible > 0) ||
      (need.nonFungible && !got.nonFungible && has.nonFungible) ||
      (need.inflation > got.inflation && has.inflation > 0) || (need.link && !got.link && has.link) ||
      (need.mint > got.mint && has.mint > 0)
    if !useful then continue
    picked := picked ++ [t]
    got := (held l).foldl (fun c a => c.add a.assignment) got
  if !got.enough need then throw (.insufficientAssignments assetId got.fungible)
  return picked

/-- State allocated on a UTXO in the stash, for one contract. -/
def stashState (w : Wallet) (cid : ContractId) (o : Outpoint) : List (Opout × AllocatedState) :=
  (w.stock.allocationsAt cid [o]).map fun (_, op, st) => (op, st)

def contractIdOf? (w : Wallet) (assetId : String) : Option ContractId :=
  (w.stock.geneses.find? fun g => toString g.contractId == assetId).map (·.contractId)

/-- Typed assignments of one type from a list of seals and states. -/
def typedAssigns (states : List (BuilderSeal GraphSeal × AllocatedState)) : TypedAssigns GraphSeal :=
  match states.head? with
  | some (_, .void) => .declarative (states.map (·.1))
  | some (_, .data _) => .structured (states.filterMap fun (s, st) => match st with
      | .data d => some (s, d) | _ => none)
  | _ => .fungible (states.filterMap fun (s, st) => match st with
      | .amount v => some (s, ⟨v⟩) | _ => none)

/-- The wallet assignment of a stash state. -/
def assignmentOf (o : Opout) (st : AllocatedState) : Assignment :=
  match st with
  | .amount v => if o.ty == Schemas.osInflation then .inflationRight v else .fungible v
  | .data _ => .nonFungible
  | .void => if o.ty == Schemas.osMint then .mintRight else .linkRight


/-- Rows of an outgoing operation (`save_transfers`): the batch with the operation key, the
colorings, and per recipient a transfer with its proxy data, its recipient proxy endpoints and,
for a proxy recipient, the sender proxy endpoint. `hashes` are the consignment hashes by asset
once the consignments exist. -/
def saveTransfers (w : Wallet) (op : PendingOp) (status : TransferStatus)
    (hashes : List (String × String) := []) : Wallet := Id.run do
  let tx := op.tx
  let (bi, db) := w.db.fresh
  let batch : DbBatchTransfer :=
    { idx := bi, txid := some tx.txid, status, createdAt := op.createdAt
      updatedAt := op.createdAt, expiration := op.expiration
      minConfirmations := op.minConfirmations, incoming := false
      operationSecretKey := op.operationSecretKey }
  let senderPk := op.operationSecretKey.map fun s => (⟨s⟩ : ProxyCrypto.SecretKey).pk
  let senderUrl := op.senderTransportEndpoint.bind fun e =>
    (TransportEndpoint.new e).toOption.map (·.endpoint)
  let mut db := { db with batchTransfers := db.batchTransfers ++ [batch] }
  if status == .initiated || status == .waitingCounterparty then
    db := { db with reserved := db.reserved ++ tx.inputs.map fun i => ⟨i.prevout, none, some bi⟩ }
  -- colored outputs of the witness (change) are registered before broadcast
  for (o, i) in tx.outputs.zipIdx do
    if w.isColored o.script then db := (db.setTxo (tx.outpoint i) o.value.toNat (exists_ := false)).2
  let fascia := op.fascia.getD default
  for (cid, b) in fascia.bundles.toList do
    let assetId := toString cid
    let userDriven := op.recipients.any (·.1 == assetId)
    let (ati, d) := db.fresh
    let kind := if userDriven then op.kind.getD .transfer else .transfer
    db := { d with
      assetTransfers := d.assetTransfers ++ [⟨ati, userDriven, bi, some assetId, some kind⟩] }
    for kt in b.knownTransitions do
      -- inputs: the spent allocations
      for inp in kt.transition.inputs do
        for (op', o, st) in (w.stock.allocations cid).filter (·.2.1 == inp) |>.map fun x => (x.2.1, x.1, x.2.2) do
          let _ := op'
          if let some t := db.txo? o then
            let (ci, d) := db.fresh
            db := { d with colorings := d.colorings ++ [⟨ci, t.idx, ati, .input, assignmentOf inp st⟩] }
      -- change: revealed seals back to the wallet
      for (ty, ta) in kt.transition.assignments.toList do
        for (bs, st) in ta.items do
          if let some g := bs.revealed? then
            let o := g.outpointOr tx.txid
            let mine := (db.txo? o).isSome
            if mine then
              let t := (db.txo? o).getD default
              let (ci, d) := db.fresh
              db := { d with colorings := d.colorings ++
                [⟨ci, t.idx, ati, .change, assignmentOf ⟨kt.opid, ty, 0⟩ (.ofRevealed st)⟩] }
    for lr in (op.recipients.lookup assetId).getD [] do
      let (ti, d) := db.fresh
      let proxyTransferId := match senderPk, lr.publicKey with
        | some spk, some _ => some (lr.proxyIds spk).2
        | _, _ => none
      let tr : DbTransfer :=
        { idx := ti, assetTransferIdx := ati, requestedAssignment := some lr.assignment
          recipientId := some lr.recipientId, recipientPubkey := lr.publicKey
          consignmentHash := hashes.lookup assetId, recipientEncryption := lr.encryption
          proxyTransferId, invoiceExpiration := lr.invoiceExpiration }
      db := { d with
        transfers := d.transfers ++ [tr]
        endpoints := d.endpoints ++
          lr.endpoints.map fun e => ⟨ti, e.endpoint, .recipientProxy, e.used⟩ }
      if !lr.endpoints.isEmpty then
        if let some url := senderUrl then db := db.saveSenderProxy ti url
  return { w with db }

/-- `update_or_save_transfers`: the batch a non-dry-run begin saved gets its new status, the
consignment hashes its transfers miss and, with `syncUsed`, the `used` flags of the recipient
proxy endpoints the consignments were posted to; after a dry-run begin the rows are saved now. -/
def updateOrSaveTransfers (w : Wallet) (op : PendingOp) (status : TransferStatus)
    (hashes : List (String × String)) (now : Nat) (syncUsed : Bool := true) : Wallet :=
  match w.db.batchByTxid? op.txid false with
  | none => w.saveTransfers op status hashes
  | some b =>
    let db := w.db.updateBatch b.idx fun x => { x with status, updatedAt := now }
    let backfill (db : Db) (a : DbAssetTransfer) : Db :=
      match a.assetId.bind fun id => hashes.lookup id with
      | none => db
      | some h => (db.transfersOf a.idx).foldl (fun db t =>
          if t.consignmentHash.isSome then db
          else db.updateTransfer t.idx fun t => { t with consignmentHash := some h }) db
    let db := (db.assetTransfersOf b.idx).foldl backfill db
    let locals := op.recipients.flatMap (·.2)
    let setUsed (db : Db) (t : DbTransfer) : Db :=
      match locals.find? (some ·.recipientId == t.recipientId) with
      | none => db
      | some lr => (db.recipientProxiesOf t.idx).foldl (fun db e =>
          db.setEndpointUsed t.idx e.endpoint
            ((lr.endpoints.find? (·.endpoint == e.endpoint)).any (·.used))) db
    { w with db := if syncUsed then (db.transfersOfBatch b.idx).foldl setUsed db else db }

/-- `ChangeSlots`: a UTXO holds a mint right of an asset when one of its allocations does or one
of its unpaid invoices requests one. -/
def holdsMintRight (w : Wallet) (assetId : String) (o : Outpoint) : Bool :=
  (((w.db.txo? o).map w.db.allocationsOn).any fun l =>
    l.any fun a => a.assetId == some assetId && a.assignment == .mintRight && a.held) ||
  (w.db.unpaidInvoices o).any fun t => t.requestedAssignment == some .mintRight &&
    (w.db.assetTransfers.find? (·.idx == t.assetTransferIdx)).any (·.assetId == some assetId)

/-- `take_change_seal` of a mint right: the first change destination (`none`: the bitcoin change)
that holds no mint right of the asset and took none in this operation (`taken`). -/
def mintRightDest (w : Wallet) (dests : List (Option Outpoint)) (assetId : String)
    (taken : List (String × Option Outpoint)) : Result (Option Outpoint) :=
  let free (d : Option Outpoint) : Bool :=
    !taken.contains (assetId, d) && !(d.any (w.holdsMintRight assetId))
  match dests.find? free with
  | some d => .ok d
  | none => .error .insufficientAllocationSlots

/-- Build the witness transaction of an RGB operation: when the selected inputs
cannot pay outputs and fee, add empty colored UTXOs, largest first; with none
left the operation fails with `insufficientAllocationSlots`. -/
def buildColoredTx (w : Wallet) (selected : List DbTxo) (outs : List TxOut) (change : Script)
    (feeRate : Nat) (now : Option Nat := none) : Result (Tx × List DbTxo) := Id.run do
  let mut selected := selected
  let mut extra := (w.availableAllocations (selected.map (·.outpoint)) (some 0) now).mergeSort
    fun a b => a.1.btcAmount ≥ b.1.btcAmount
  for _ in List.range (extra.length + 1) do
    match buildTx (selected.map fun t => (t.outpoint, t.btcAmount)) outs change feeRate with
    | .ok tx => return .ok (tx, selected)
    | .error (.insufficientBitcoins _ _) =>
      match extra with
      | [] => return .error .insufficientAllocationSlots
      | (t, _, _) :: rest => selected := selected ++ [t]; extra := rest
    | .error e => return .error e
  return .error .insufficientAllocationSlots

/-- Prepare a send (`send_begin`): checks, selection, transaction and coloring.
`recipientMap` maps asset ids to their recipients. The proxies it asks (`server.info`,
`invoice.check`) do not change, so no world is returned. -/
def sendBegin (w : Wallet) (world : World) (o : Online) (recipientMap : List (String × List Recipient))
    (donation : Bool) (feeRate : Nat) (minConfirmations : Nat) (expiration : Nat)
    (senderEndpoint : Option String := none) (dryRun : Bool := false) : Result (Wallet × PendingOp) := do
  w.checkOnline o
  let now := world.now
  if recipientMap.isEmpty || recipientMap.any (·.2.isEmpty) then throw .invalidRecipientMap
  checkOperationExpiration now expiration
  if let some e := senderEndpoint then discard (TransportEndpoint.new e)
  let (opKey, w) := w.newOperationKey now
  checkFeeRate feeRate
  let mut locals : List (String × List LocalRecipient) := []
  let mut vout := 1
  let mut i := 0
  for (assetId, rs) in recipientMap do
    let a ← w.asset? assetId
    w.checkSchemaSupport a.schema
    let mut ls : List LocalRecipient := []
    for r in rs do
      if !r.transportEndpoints.isEmpty && senderEndpoint.isNone then
        throw (.invalidTransportEndpoint "missing sender transport endpoint")
      let lr ← w.parseRecipient now a.schema r vout i opKey
      if lr.vout.isSome then vout := vout + 1
      i := i + 1
      if lr.assignment == .linkRight && ls.any (·.assignment == .linkRight) then
        throw (.invalidRecipientData "the link right can only be sent to a single recipient")
      ls := ls ++ [lr]
    locals := locals ++ [(assetId, ls)]
  let invoiceExps : List Nat := (locals.flatMap (·.2)).filterMap (·.invoiceExpiration)
  if !donation then
    if let some m := invoiceExps.min? then
      if expiration + invoiceExpirationMarginSecs > m then throw .invalidExpiration
  let usable := usableEndpoints world (locals.flatMap (·.2))
  locals := locals.map fun (a, ls) => (a, ls.map (·.markUsable usable))
  checkUsableEndpoints (locals.flatMap (·.2))
  let ids := (locals.flatMap (·.2)).map (·.recipientId)
  if ids.eraseDups.length != ids.length then throw .recipientIdDuplicated
  -- input selection, per asset in ascending id order
  let cands := w.inputUnspents (some now)
  let sortedAssets := locals.mergeSort fun a b => a.1 ≤ b.1
  let mut selected : List DbTxo := []
  for (assetId, ls) in sortedAssets do
    let need0 := AssignmentsCollection.ofList (ls.map (·.assignment))
    let need := { need0 with mint := min need0.mint 1 }
    let picked ← w.selectInputs assetId need (cands.filter fun (t, _) => !selected.contains t)
    selected := selected ++ picked
  -- each proxy recipient's invoice must take a transfer on one of its usable proxies
  for lr in locals.flatMap (·.2) do
    if lr.endpoints.isEmpty then continue
    let servers :=
      (lr.endpoints.filter (·.usable)).filterMap fun e => world.proxies.lookup e.endpoint
    Proxy.checkInvoiceAvailable servers (lr.proxyIds "").1
  -- bitcoin side: OP_RETURN, witness outputs, colored change; add empty UTXOs to pay the fee
  let witnessOuts := (locals.flatMap (·.2)).filterMap fun lr => match lr.beneficiary with
    | .witnessVout s => some (⟨lr.amountSat.toUInt64, s⟩ : TxOut)
    | _ => none
  let (changeScript, w) := w.coloredOutputAddress
  let (tx0, sel) ←
    w.buildColoredTx selected (⟨0, .opReturn none⟩ :: witnessOuts) changeScript feeRate (some now)
  selected := sel
  let changeVout? : Option Nat :=
    if tx0.outputs.length > 1 + witnessOuts.length then some (1 + witnessOuts.length) else none
  -- change destinations: the bitcoin change output (`none`), then existing UTXOs with room
  let free := (w.availableAllocations (selected.map (·.outpoint)) (now := some now)).map
    fun (t, _, _) => some t.outpoint
  let dests : List (Option Outpoint) := (if changeVout?.isSome then [none] else []) ++ free
  let sealAt (d : Option Outpoint) (k : Nat) : GraphSeal :=
    let blinding := now.toUInt64 * 13 + k.toUInt64
    match d with
    | none => GraphSeal.witnessVout (changeVout?.getD 0).toUInt32 blinding
    | some o => GraphSeal.ofOutpoint o blinding
  let slotSeal (k : Nat) : GraphSeal := sealAt (dests.headD none) k
  if dests.isEmpty then throw .insufficientAllocationSlots
  -- coloring: per asset and assignment type one transition of the type's default
  -- transition, paying the recipients of that type with the change back; state of
  -- any contract left on the spent UTXOs moves to change, each mint right on its own
  let mut bundles : List (ContractId × List Transition) := []
  let mut k := 0
  let mut rightsTaken : List (String × Option Outpoint) := []
  let spent := selected.map (·.outpoint)
  for (assetId, ls) in sortedAssets do
    let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
    let some g := w.stock.genesis? cid | throw (.assetNotFound assetId)
    let defaultTt (ty : AssignmentType) : TransitionType :=
      ((w.stock.rules? g.schemaId).bind fun r => r.schema.defaultTransitionFor? ty).getD Schemas.tsTransfer
    let states := spent.flatMap fun op => w.stashState cid op
    let types := ((states.map (·.1.ty)) ++ ls.filterMap (·.assignment.assignmentType?)).eraseDups
    let mut ts : List Transition := []
    let mut moves : List Transition := []
    for ty in types do
      let allOfType := states.filter (·.1.ty == ty)
      let tyRecips := ls.filter (·.assignment.assignmentType? == some ty)
      -- the mint rights the recipients do not take move as extra state
      let tyStates := if ty == Schemas.osMint then allOfType.take tyRecips.length else allOfType
      for (opout, st) in allOfType.drop tyStates.length do
        let d ← w.mintRightDest dests assetId rightsTaken
        rightsTaken := rightsTaken ++ [(assetId, d)]
        let moved := OrdMap.ofList [(ty, typedAssigns [(.revealed (sealAt d k), st)])]
        moves := moves ++ [{ contractId := cid, transitionType := defaultTt ty, inputs := [opout]
                             assignments := moved }]
        k := k + 1
      let outs : List (BuilderSeal GraphSeal × AllocatedState) := tyRecips.map fun lr =>
        (lr.builderSeal, match lr.assignment with
          | .fungible n | .inflationRight n => .amount n
          | .nonFungible => (tyStates.headD (default, .void)).2
          | _ => .void)
      -- change: what the inputs hold beyond what the recipients take
      let total := (tyStates.filterMap (·.2.amount?)).foldl (· + ·.toNat) 0
      let paid := (tyRecips.map fun lr => lr.assignment.mainAmount + lr.assignment.inflationAmount).sum
      let isAmount := tyStates.any fun (_, st) => st.amount?.isSome
      let rightsLeft := if isAmount then 0 else tyStates.length - min tyStates.length tyRecips.length
      let mut change : List (BuilderSeal GraphSeal × AllocatedState) := []
      if isAmount && total > paid then
        change := [(.revealed (slotSeal k), .amount (total - paid).toUInt64)]
        k := k + 1
      for _ in List.range rightsLeft do
        change := change ++ [(.revealed (slotSeal k), (tyStates.headD (default, .void)).2)]
        k := k + 1
      if !tyStates.isEmpty then
        ts := ts ++ [{ contractId := cid, transitionType := defaultTt ty, inputs := tyStates.map (·.1)
                       assignments := OrdMap.ofList [(ty, typedAssigns (outs ++ change))] }]
    bundles := bundles ++ [(cid, ts ++ moves)]
  -- extra allocations of other contracts on the spent UTXOs
  for g in w.stock.geneses do
    let cid := g.contractId
    if !(bundles.any (·.1 == cid)) then
      let states := spent.flatMap fun op => w.stashState cid op
      let mut ts : List Transition := []
      for (opout, st) in states do
        let ty := opout.ty
        let tt := (((w.stock.rules? g.schemaId).bind fun r => r.schema.defaultTransitionFor? ty)).getD Schemas.tsTransfer
        let s ← if ty == Schemas.osMint then do
            let d ← w.mintRightDest dests (toString cid) rightsTaken
            rightsTaken := rightsTaken ++ [(toString cid, d)]
            pure (sealAt d k)
          else pure (slotSeal k)
        ts := ts ++ [{ contractId := cid, transitionType := tt, inputs := [opout]
                       assignments := OrdMap.ofList [(ty, typedAssigns [(.revealed s, st)])] }]
        k := k + 1
      if !ts.isEmpty then bundles := bundles ++ [(cid, ts)]
  let fascia ← (commitBundles tx0 (bundles.map fun (c, ts) => (c, TransitionBundle.ofTransitions ts))
    (now.toUInt64)).mapError fun e => .internal (reprStr e)
  let tx := fascia.sealWitness.tx
  let op : PendingOp := { txid := tx.txid, tx, fascia := some fascia, kind := some .transfer, donation
                          minConfirmations, expiration := some expiration
                          recipients := sortedAssets, senderTransportEndpoint := senderEndpoint
                          operationSecretKey := some opKey.seed, createdAt := now }
  -- database rows
  let mut w := { w with pending := (w.pending.filter (·.txid != tx.txid)) ++ [op] }
  if !dryRun then w := (saveTransfers w op .initiated).updateBackupInfo now
  return (w, op)

/-- Broadcast an operation and consume its fascia (`broadcast_batch`). -/
def broadcastOp (w : Wallet) (bi : Nat) : Net Wallet := do
  let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
  let some t := b.txid | throw (.internal "missing txid")
  let some op := w.pending.find? (·.txid == t) | throw (.unknownTransfer (toString t))
  broadcastTx op.tx
  let stock ← match op.fascia with
    | some f =>
      Net.ofResult ((w.stock.consumeFascia f .tentative).mapError fun e => .internal (reprStr e))
    | none => pure w.stock
  let now ← Net.now
  let db := (w.db.markBroadcast op.tx).updateBatch bi fun b =>
    { b with status := .waitingConfirmations, updatedAt := now }
  return { w with db, stock }

/-- `broadcast_batch` as a call of its own. -/
def broadcastBatch (w : Wallet) (world : World) (bi : Nat) : Result (Wallet × World) :=
  let (r, world) := (w.broadcastOp bi).exec world
  r.map (·, world)

/-- Errors of `consignment.post` after which another endpoint of the recipient is tried, the
last one being reported when none takes the transfer. -/
def postRefusals : List Error :=
  [.invoiceNotReserved, .invoiceExpired, .invoiceQuotaExceeded, .transferIdDeleted, .proxyDraining]

/-- `post_transfer_data`: post an asset's consignment for each proxy recipient, encrypted for it
unless it does not support encryption, to the first usable endpoint that takes it, with the
proof of work the proxy asks for. A recipient no endpoint takes fails the send; a proxy that
does not answer aborts it. The model's contracts carry no media. -/
def postTransferData (recipients : List LocalRecipient) (c : Consignment)
    (sender : ProxyCrypto.SecretKey) (senderEndpoint : Option String) (consignmentHash : String)
    (batch : Bool) : Net (List LocalRecipient) := do
  let now ← Net.now
  let mut out : List LocalRecipient := []
  for lr in recipients do
    if lr.endpoints.isEmpty then
      out := out ++ [lr]
      continue
    let some se := senderEndpoint | throw (.internal "missing sender transport endpoint")
    let key := (ProxyCrypto.deriveShared sender (lr.publicKey.getD "")).symKey
    let file := ProxyCrypto.Blob.forRecipient lr.encryption key (.consignment c)
    let post := Proxy.ConsignmentPost.make sender (lr.proxyIds sender.pk).1 se consignmentHash batch
      file now
    let mut eps := lr.endpoints
    let mut refusal : Option Error := none
    let mut found := false
    for (e, j) in lr.endpoints.zipIdx do
      if !e.usable then continue
      let s ← ProxyClient.proxyAt e.endpoint
      match s.postConsignmentWithPow post now with
      | .ok s' =>
        ProxyClient.storeProxy e.endpoint s'
        eps := eps.set j { e with used := true }
        found := true
        break
      | .error err =>
        if postRefusals.contains err then refusal := some err
        else if err matches .proxyCannotChange _ then throw err
    if !found then throw (refusal.getD .noValidTransportEndpoint)
    out := out ++ [{ lr with endpoints := eps }]
  return out

/-- `ack.prepare` on the sender proxy (`send_end`): the operation with the signed transaction
encrypted for each proxy recipient. A cleared signed transaction is not an error; an expiration
the proxy refuses is, unless the proxy knows the operation already (then nothing is posted).
Gives the broadcast deadline and whether the operation expired. -/
def prepareAck (w : Wallet) (op : PendingOp) (sender : ProxyCrypto.SecretKey)
    (hashes : List (String × String)) : Net (Option Nat × Bool) := do
  let proxyRecipients := op.recipients.flatMap fun (a, ls) =>
    (ls.filter (!·.endpoints.isEmpty)).map (a, ·)
  if op.donation || proxyRecipients.isEmpty then return (none, false)
  let txHash := (ProxyCrypto.Payload.tx op.tx).hash
  let transferData := proxyRecipients.map fun (a, lr) =>
    ((lr.proxyIds sender.pk).2,
      Proxy.AckTransferData.make sender (lr.publicKey.getD "") ((hashes.lookup a).getD "") op.tx)
  let some expiration := op.expiration | throw (.internal "missing expiration")
  let some se := op.senderTransportEndpoint
    | throw (.internal "missing sender transport endpoint")
  let url := (← Net.ofResult (TransportEndpoint.new se)).endpoint
  let grace ← ProxyClient.senderRetentionGrace url
  let s ← ProxyClient.proxyAt url
  let message := Proxy.Msg.prepareAckAuth sender.pk (toString expiration) txHash transferData
  let prep : Proxy.AckPrepare :=
    { transferData, expiresAt := expiration, signedTxHash := txHash, senderPk := sender.pk
      signature := ProxyClient.authSignature w.proxyAuthKeys url message }
  match s.ackPrepare prep with
  | .ok s' =>
    ProxyClient.storeProxy url s'
    return (some (expiration + grace), false)
  | .error .signedTxCleared => return (some (expiration + grace), false)
  | .error .expirationInvalid =>
    let r ← ProxyClient.getAck url (transferData.map (·.1)) sender
    if !(← Net.ofResult (Proxy.senderProxyKnowsOperation (Proxy.errorOf? r))) then
      throw .expirationInvalid
    return (some (expiration + grace), true)
  | .error e => throw e

/-- `send_end` as a step: consignments, `ack.prepare` and the posts for proxy recipients, then a
donation is broadcast and waits for confirmations while a transfer waits for the ACKs. -/
def sendEndStep (w : Wallet) (txid : Txid) : Net (Wallet × List (String × Consignment)) := do
  if let some b := w.db.batchByTxid? txid false then
    if b.status != .initiated && b.status != .waitingCounterparty then
      throw (.cannotEndTransfer (toString txid))
  let some op := w.pending.find? (·.txid == txid) | throw (.unknownTransfer (toString txid))
  if op.kind != some .transfer then throw (.wrongOperation (toString txid))
  let some fascia := op.fascia | throw (.internal "missing fascia")
  -- one consignment per asset with recipients
  let mut cons : List (String × Consignment) := []
  for (assetId, ls) in op.recipients do
    let some cid := w.contractIdOf? assetId | continue
    let secrets := ls.filterMap fun lr => match lr.beneficiary with
      | .blindedSeal s => some s
      | _ => none
    let outs := ls.filterMap fun lr => match lr.beneficiary, lr.vout with
      | .witnessVout _, some v => some (op.tx.outpoint v)
      | _, _ => none
    let c ← Net.ofResult ((w.stock.transferFromFascia cid outs secrets [] fascia).mapError
      fun e => .internal (reprStr e))
    cons := cons ++ [(assetId, c)]
  let some seed := op.operationSecretKey | throw (.internal "missing operation secret key")
  let sender : ProxyCrypto.SecretKey := ⟨seed⟩
  let batch := (op.recipients.map (·.2.length)).sum > 1
  let hashes := cons.map fun (a, c) => (a, (ProxyCrypto.Payload.consignment c).hash)
  let (deadline, expired) ← w.prepareAck op sender hashes
  let mut recipients := op.recipients
  if !expired then
    recipients ← op.recipients.mapM fun (a, ls) => do
      let some c := cons.lookup a | return (a, ls)
      return (a, ← postTransferData ls c sender op.senderTransportEndpoint
        ((hashes.lookup a).getD "") batch)
  let op : PendingOp := { op with consignments := cons, recipients }
  let now ← Net.now
  let w : Wallet :=
    { w with pending := w.pending.map fun (p : PendingOp) => if p.txid == txid then op else p }
  if op.donation then
    let w := w.updateOrSaveTransfers op .waitingConfirmations hashes now
    let bi := ((w.db.batchByTxid? txid false).map (·.idx)).getD 0
    return (← w.broadcastOp bi, cons)
  let w := w.updateOrSaveTransfers op .waitingCounterparty hashes now
  let bi := ((w.db.batchByTxid? txid false).map (·.idx)).getD 0
  let db := match deadline with
    | some d => w.db.updateBatch bi fun b => { b with broadcastDeadline := some d }
    | none => w.db
  return ({ w with db }, cons)

/-- End a send (`send_end`). -/
def sendEnd (w : Wallet) (world : World) (o : Online) (txid : Txid) :
    Result (Wallet × World × List (String × Consignment)) := do
  w.checkOnline o
  let (r, world) := (w.sendEndStep txid).exec world
  let (w, cons) ← r
  return (w.updateBackupInfo world.now, world, cons)

end Wallet

end Rgb.Lib
