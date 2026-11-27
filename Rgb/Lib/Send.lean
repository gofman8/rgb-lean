import Rgb.Lib.Receive

/-!
# Sending

`send_begin` checks the recipients, selects inputs, builds the witness
transaction (output 0 `OP_RETURN`, then one output per witness recipient, then
bitcoin change to a colored address) and colors it: per asset one transition
paying the recipients with the change back to the wallet, plus one transition
per other allocation that sits on a spent UTXO, moving it to a change slot (state
on a spent output that no transition moves is lost). The bundles are committed in
the `OP_RETURN` output. `send_end` takes the signed transaction, builds one
consignment per asset for the recipients, and either broadcasts at once
(donation) or waits for the recipients' ACK.

Model simplifications: all state of the asset on a selected UTXO is spent (not
only the part that covers the need); signing returns the unsigned transaction.
-/

namespace Rgb.Lib

/-- A recipient after its checks (`LocalRecipient`). -/
structure LocalRecipient where
  recipientId : String
  beneficiary : Beneficiary
  assignment : Assignment
  /-- Witness output index (witness recipients). -/
  vout : Option Nat := none
  amountSat : Nat := 0
  blinding : UInt64 := 0
  endpoints : List String := []
  invoiceExpiration : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

namespace Wallet

/-- Operation expiration (`check_operation_expiration`): at least 300 s and at most ten years ahead. -/
def checkOperationExpiration (now e : Nat) : Result Unit :=
  if e < now + proxyClockSkewMarginSecs || e > now + maxExpirationSecs then .error .invalidExpiration
  else .ok ()

/-- Recipient checks (`parse_recipient`), in order. -/
def parseRecipient (w : Wallet) (now : Nat) (schema : AssetSchema) (r : Recipient) (vout : Nat) (i : Nat) :
    Result LocalRecipient := do
  if !schema.supportsAssignment r.assignment then throw .invalidAssignment
  if r.assignment == .fungible 0 || r.assignment == .inflationRight 0 then throw .invalidAmountZero
  let (net, b) ← Beneficiary.parse r.recipientId
  if net != w.chainNet then throw .invalidRecipientNetwork
  if !r.transportEndpoints.isEmpty then
    checkReceiveEndpoints r.transportEndpoints
    if r.publicKey.isNone then throw (.invalidPubkey "missing recipient public key")
    match r.expirationTimestamp with
    | none => throw (.invalidRecipientData "missing invoice expiration")
    | some e =>
      if e ≤ now then throw .invoiceExpired
      if e > now + maxExpirationSecs then throw .invalidExpiration
  match b with
  | .blindedSeal _ =>
    if r.witnessData.isSome then throw (.invalidRecipientData "cannot provide witness data for a blinded recipient")
    return ⟨r.recipientId, b, r.assignment, none, 0, 0, r.transportEndpoints, r.expirationTimestamp⟩
  | .witnessVout _ =>
    let some wd := r.witnessData | throw (.invalidRecipientData "missing witness data for a witness recipient")
    if !r.transportEndpoints.isEmpty && wd.blinding.isSome then
      throw (.invalidRecipientData "cannot provide a blinding for a witness recipient with transport endpoints")
    let blinding := wd.blinding.getD (now.toUInt64 * 31 + i.toUInt64)
    return ⟨r.recipientId, b, r.assignment, some vout, wd.amountSat, blinding, r.transportEndpoints,
      r.expirationTimestamp⟩

/-- UTXOs an RGB operation may spend (`get_input_unspents`). -/
def inputUnspents (w : Wallet) : List (DbTxo × List LocalRgbAllocation) :=
  (w.unspents.filter fun (t, allocs, pb) =>
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


/-- Rows of an outgoing operation (`save_transfers`). -/
def saveTransfers (w : Wallet) (op : PendingOp) (locals : List (String × List LocalRecipient))
    (status : TransferStatus) : Wallet := Id.run do
  let tx := op.tx
  let (bi, db) := w.db.fresh
  let batch : DbBatchTransfer :=
    { idx := bi, txid := some tx.txid, status, createdAt := 0, updatedAt := 0, expiration := op.expiration
      minConfirmations := op.minConfirmations, incoming := false, operationSecretKey := some s!"op/{bi}" }
  let mut db := { db with batchTransfers := db.batchTransfers ++ [batch] }
  if status == .initiated || status == .waitingCounterparty then
    db := { db with reserved := db.reserved ++ tx.inputs.map fun i => ⟨i.prevout, none, some bi⟩ }
  -- colored outputs of the witness (change) are registered before broadcast
  for (o, i) in tx.outputs.zipIdx do
    if w.isColored o.script then db := (db.setTxo (tx.outpoint i) o.value.toNat (exists_ := false)).2
  let fascia := op.fascia.getD default
  for (cid, b) in fascia.bundles.toList do
    let assetId := toString cid
    let userDriven := locals.any (·.1 == assetId)
    let (ati, d) := db.fresh
    db := { d with assetTransfers := d.assetTransfers ++
      [⟨ati, userDriven, bi, some assetId, some (if userDriven then .transfer else .transfer)⟩] }
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
    for lr in (locals.find? (·.1 == assetId)).map (·.2) |>.getD [] do
      let (ti, d) := db.fresh
      let tr : DbTransfer :=
        { idx := ti, assetTransferIdx := ati, requestedAssignment := some lr.assignment,
          recipientId := some lr.recipientId, invoiceExpiration := lr.invoiceExpiration }
      db := { d with
        transfers := d.transfers ++ [tr]
        endpoints := d.endpoints ++ lr.endpoints.map (⟨ti, ·, .recipientProxy, false⟩) }
  return { w with db }
/-- Build the witness transaction of an RGB operation: when the selected inputs
cannot pay outputs and fee, add empty colored UTXOs, largest first; with none
left the operation fails with `insufficientAllocationSlots`. -/
def buildColoredTx (w : Wallet) (selected : List DbTxo) (outs : List TxOut) (change : Script) (feeRate : Nat) :
    Result (Tx × List DbTxo) := Id.run do
  let mut selected := selected
  let mut extra := (w.availableAllocations (selected.map (·.outpoint)) (some 0)).mergeSort
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
`recipientMap` maps asset ids to their recipients. -/
def sendBegin (w : Wallet) (world : World) (o : Online) (recipientMap : List (String × List Recipient))
    (donation : Bool) (feeRate : Nat) (minConfirmations : Nat) (expiration : Nat)
    (senderEndpoint : Option String := none) (dryRun : Bool := false) : Result (Wallet × PendingOp) := do
  w.checkOnline o
  let now := world.now
  if recipientMap.isEmpty || recipientMap.any (·.2.isEmpty) then throw .invalidRecipientMap
  checkOperationExpiration now expiration
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
      let lr ← w.parseRecipient now a.schema r vout i
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
  let ids := (locals.flatMap (·.2)).map (·.recipientId)
  if ids.eraseDups.length != ids.length then throw .recipientIdDuplicated
  -- input selection, per asset in ascending id order
  let cands := w.inputUnspents
  let sortedAssets := locals.mergeSort fun a b => a.1 ≤ b.1
  let mut selected : List DbTxo := []
  for (assetId, ls) in sortedAssets do
    let need0 := AssignmentsCollection.ofList (ls.map (·.assignment))
    let need := { need0 with mint := min need0.mint 1 }
    let picked ← w.selectInputs assetId need (cands.filter fun (t, _) => !selected.contains t)
    selected := selected ++ picked
  -- bitcoin side: OP_RETURN, witness outputs, colored change; add empty UTXOs to pay the fee
  let witnessOuts := (locals.flatMap (·.2)).filterMap fun lr => match lr.beneficiary with
    | .witnessVout s => some (⟨lr.amountSat.toUInt64, s⟩ : TxOut)
    | _ => none
  let (changeScript, w) := w.coloredOutputAddress
  let (tx0, sel) ← w.buildColoredTx selected (⟨0, .opReturn none⟩ :: witnessOuts) changeScript feeRate
  selected := sel
  let changeVout? : Option Nat :=
    if tx0.outputs.length > 1 + witnessOuts.length then some (1 + witnessOuts.length) else none
  -- change slots: the bitcoin change output, then existing UTXOs with room
  let slotSeal (k : Nat) : GraphSeal :=
    match changeVout? with
    | some v => GraphSeal.witnessVout v.toUInt32 (now.toUInt64 * 13 + k.toUInt64)
    | none =>
      let free := w.availableAllocations (selected.map (·.outpoint))
      GraphSeal.ofOutpoint ((free.headD default).1.outpoint) (now.toUInt64 * 13 + k.toUInt64)
  if changeVout?.isNone && (w.availableAllocations (selected.map (·.outpoint))).isEmpty then
    throw .insufficientAllocationSlots
  -- coloring: per asset and assignment type one transition of the type's default
  -- transition, paying the recipients of that type with the change back; state of
  -- any contract left on the spent UTXOs moves to change
  let mut bundles : List (ContractId × List Transition) := []
  let mut k := 0
  let spent := selected.map (·.outpoint)
  for (assetId, ls) in sortedAssets do
    let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
    let some g := w.stock.genesis? cid | throw (.assetNotFound assetId)
    let defaultTt (ty : AssignmentType) : TransitionType :=
      ((w.stock.rules? g.schemaId).bind fun r => r.schema.defaultTransitionFor? ty).getD Schemas.tsTransfer
    let states := spent.flatMap fun op => w.stashState cid op
    let types := ((states.map (·.1.ty)) ++ ls.filterMap (·.assignment.assignmentType?)).eraseDups
    let mut ts : List Transition := []
    for ty in types do
      let tyStates := states.filter (·.1.ty == ty)
      let tyRecips := ls.filter (·.assignment.assignmentType? == some ty)
      let outs : List (BuilderSeal GraphSeal × AllocatedState) := tyRecips.map fun lr =>
        let bs : BuilderSeal GraphSeal := match lr.beneficiary, lr.vout with
          | .blindedSeal sec, _ => .concealed sec
          | .witnessVout _, some v => .revealed (GraphSeal.witnessVout v.toUInt32 lr.blinding)
          | .witnessVout _, none => .concealed default
        (bs, match lr.assignment with
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
    bundles := bundles ++ [(cid, ts)]
  -- extra allocations of other contracts on the spent UTXOs
  for g in w.stock.geneses do
    let cid := g.contractId
    if !(bundles.any (·.1 == cid)) then
      let states := spent.flatMap fun op => w.stashState cid op
      let mut ts : List Transition := []
      for (opout, st) in states do
        let ty := opout.ty
        let tt := (((w.stock.rules? g.schemaId).bind fun r => r.schema.defaultTransitionFor? ty)).getD Schemas.tsTransfer
        ts := ts ++ [{ contractId := cid, transitionType := tt, inputs := [opout]
                       assignments := OrdMap.ofList [(ty, typedAssigns [(.revealed (slotSeal k), st)])] }]
        k := k + 1
      if !ts.isEmpty then bundles := bundles ++ [(cid, ts)]
  let fascia ← (commitBundles tx0 (bundles.map fun (c, ts) => (c, TransitionBundle.ofTransitions ts))
    (now.toUInt64)).mapError fun e => .internal (reprStr e)
  let tx := fascia.sealWitness.tx
  let op : PendingOp := { txid := tx.txid, tx, fascia := some fascia, kind := some .transfer, donation
                          minConfirmations, expiration := some expiration }
  -- database rows
  let mut w := { w with pending := (w.pending.filter (·.txid != tx.txid)) ++ [op] }
  if !dryRun then w := saveTransfers w op locals .initiated
  return (w, op)

/-- Broadcast an operation and consume its fascia (`broadcast_batch`). -/
def broadcastBatch (w : Wallet) (world : World) (bi : Nat) : Result (Wallet × World) := do
  let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
  let some t := b.txid | throw (.internal "missing txid")
  let some op := w.pending.find? (·.txid == t) | throw (.unknownTransfer (toString t))
  let chain ← (world.chain.broadcast op.tx).mapError broadcastError
  let stock ← match op.fascia with
    | some f => (w.stock.consumeFascia f .tentative).mapError fun e => .internal (reprStr e)
    | none => pure w.stock
  let db := (w.db.markBroadcast op.tx).updateBatch bi fun b => { b with status := .waitingConfirmations }
  return ({ w with db, stock }, { world with chain })


/-- End a send (`send_end`): build the consignments; a donation is broadcast at
once and waits for confirmations, otherwise the transfer waits for the ACKs. -/
def sendEnd (w : Wallet) (world : World) (o : Online) (txid : Txid) :
    Result (Wallet × World × List (String × Consignment)) := do
  w.checkOnline o
  if let some b := w.db.batchByTxid? txid false then
    if b.status != .initiated && b.status != .waitingCounterparty then throw (.cannotEndTransfer (toString txid))
  let some op := w.pending.find? (·.txid == txid) | throw (.unknownTransfer (toString txid))
  if op.kind != some .transfer then throw (.wrongOperation (toString txid))
  let some fascia := op.fascia | throw (.internal "missing fascia")
  let mut w := w
  if (w.db.batchByTxid? txid false).isNone then
    w := saveTransfers w op ((w.db.transfers.filterMap fun _ => none) : List (String × List LocalRecipient))
      .initiated
  let batch := (w.db.batchByTxid? txid false).getD default
  -- one consignment per asset with recipients
  let mut cons : List (String × Consignment) := []
  for at_ in w.db.assetTransfersOf batch.idx do
    if at_.userDriven then
      let some assetId := at_.assetId | continue
      let some cid := w.contractIdOf? assetId | continue
      let recips := (w.db.transfersOf at_.idx).filterMap (·.recipientId)
      let parsed := recips.filterMap fun r => (Beneficiary.parse r).toOption.map (·.2)
      let secrets := parsed.filterMap fun b => match b with | .blindedSeal s => some s | _ => none
      let outs := parsed.filterMap fun b => match b with
        | .witnessVout s => (op.tx.outputs.zipIdx.find? (·.1.script == s)).map fun (_, i) => op.tx.outpoint i
        | _ => none
      let c ← (w.stock.transferFromFascia cid outs secrets [] fascia).mapError fun e => .internal (reprStr e)
      cons := cons ++ [(assetId, c)]
  w := { w with pending := w.pending.map fun p => if p.txid == txid then { p with consignments := cons } else p }
  if op.donation then
    let (w', world') ← w.broadcastBatch world batch.idx
    return (w', world', cons)
  else
    w := { w with db := w.db.updateBatch batch.idx fun b => { b with status := .waitingCounterparty } }
    return (w, world, cons)

end Wallet

end Rgb.Lib
