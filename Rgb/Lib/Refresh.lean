import Rgb.Lib.Send

/-!
# Refresh, out-of-band exchange, failing and deleting transfers

`refresh` moves every waiting transfer forward. A receiver checks a received
consignment (`process_received_consignment`): known and supported schema, the
asset it asked for, consensus validity, exactly one payment to its seal or
address carrying exactly one allocation, not already received, and room on the
receiving UTXO. A valid payment is ACKed and waits for the witness to be
broadcast and confirmed; an invalid one fails the receive. Once the witness has
the required confirmations, the receiver's stash accepts the consignment and the
transfer is settled; the sender's transfer settles the same way.

Without transport endpoints the consignment and the ACK are handed over out of
band (`provide_out_of_band_consignment`, `provide_out_of_band_ack`).

A transfer that may still move cannot always be failed: `fail_transfers` only
fails transfers in a fallible status, and only when no counterparty can still
complete them. Only failed transfers can be deleted.
-/

namespace Rgb.Lib

namespace Wallet

/-- Confirmations of a transaction; none when the chain does not know it. -/
def confirmationsOf (c : Chain) (t : Txid) : Option Nat :=
  match c.witnessOrd t with
  | .archived => none
  | _ => some (c.confirmations t)

/-- Fail a batch (`fail_batch_transfer`): unflag pending witness outputs, drop reservations. -/
def failBatch (w : Wallet) (now bi : Nat) : Wallet :=
  let db := w.db.updateBatch bi fun b => { b with status := .failed, updatedAt := now }
  let txid := (db.batch? bi).bind (·.txid)
  { w with db := { db with
      reserved := db.reserved.filter (·.forColored != some bi)
      txos := db.txos.map fun t => if txid == some t.outpoint.txid then { t with pendingWitness := false } else t } }

/-- An asset row from a received genesis. -/
def assetRowOf (schema : AssetSchema) (g : Genesis) (now : Nat) : DbAsset :=
  let glob (t : GlobalStateType) : Option StrictValue := ((g.globals.find? t).bind (·.head?)).map (·.v)
  let spec := match glob Schemas.gsNominal with
    | some (.assetSpec s) => some s
    | _ => none
  let issued := match glob Schemas.gsIssuedSupply with
    | some (.amount v) => v.toNat
    | _ => if schema == .uda then 1 else 0
  { idx := 0, id := toString g.contractId, schema, addedAt := now
    name := (spec.map (·.name.s)).getD (match glob Schemas.gsName with | some (.name n) => n.s | _ => "")
    ticker := spec.map (·.ticker.s), details := none
    precision := (spec.map (·.precision.decimals)).getD 0, initialSupply := issued, timestamp := g.timestamp }

/-- Which outputs of a consignment pay the receiver (`find_payments`): per bundle,
the assignments to the receiver's seal or address not spent within the consignment. -/
def findPayments (c : Consignment) (b : Beneficiary) : List (Txid × Nat × List (Opout × AllocatedState)) :=
  let spent := c.bundles.flatMap fun wb => wb.bundle.knownTransitions.flatMap (·.transition.inputs)
  c.bundles.filterMap fun wb =>
    let tx := wb.tx
    let hits := wb.bundle.knownTransitions.flatMap fun kt =>
      kt.transition.assignments.toList.flatMap fun (ty, ta) =>
        ta.items.zipIdx.filterMap fun ((bs, st), no) =>
          let opout : Opout := ⟨kt.opid, ty, no.toUInt16⟩
          let hit := match b, bs.revealed? with
            | .blindedSeal s, _ => bs.toSecret == s
            | .witnessVout script, some g =>
              g.txptr == .witnessTx && (tx.outputAt? g.vout).any (·.script == script)
            | .witnessVout _, none => false
          if hit && !spent.contains opout then
            some (opout, AllocatedState.ofRevealed st, match bs.revealed? with | some g => g.vout.toNat | none => 0)
          else none
    if hits.isEmpty then none
    else some (tx.txid, (hits.headD default).2.2, hits.map fun (o, st, _) => (o, st))

/-- Accept or refuse a received consignment for an incoming batch
(`process_received_consignment`, out-of-band mode). Returns the new status. -/
def processReceived (w : Wallet) (world : World) (bi : Nat) (c : Consignment) :
    Result (Wallet × World × TransferStatus) := do
  let now := world.now
  let refuse (w : Wallet) : Result (Wallet × World × TransferStatus) := .ok (w.failBatch now bi, world, .failed)
  let some batch := w.db.batch? bi | throw (.batchTransferNotFound bi)
  let some at_ := (w.db.assetTransfersOf bi).head? | throw (.internal "missing asset transfer")
  let some tr := (w.db.transfersOf at_.idx).head? | throw (.internal "missing transfer")
  let schema? := AssetSchema.all.find? fun s => s.rules.schema.schemaId == c.schemaId
  let some schema := schema? | throw (.unknownRgbSchema (toString c.schemaId))
  if !w.data.supportedSchemas.contains schema then return ← refuse w
  if let some id := at_.assetId then
    if id != toString c.contractId then return ← refuse w
  let some rid := tr.recipientId | throw (.internal "missing recipient id")
  let (_, beneficiary) ← Beneficiary.parse rid
  let tip := world.chain.height
  let safeHeight := tip + 1 - min batch.minConfirmations tip
  let cfg : ValidationConfig := { chainNet := w.chainNet, safeHeight := some safeHeight }
  let rules := schema.rules
  let pv ← match c.validateDeterministic true rules cfg with
    | .ok pv => pure pv
    | .error (.invalidConsignment _) => return ← refuse w
    | .error e => throw (.consignmentValidationFailed (reprStr e))
  let payments := findPayments c beneficiary
  if payments.length != 1 then return ← refuse w
  let (txid, vout, receiving) := payments.headD default
  -- already received with the same transaction
  let dup := w.db.transfers.any fun t => t.idx != tr.idx && t.recipientId == some rid &&
    (w.db.batchOfAssetTransfer? t.assetTransferIdx).any fun b => b.incoming && b.status != .failed && b.txid == some txid
  if dup then return ← refuse w
  if receiving.length != 1 then return ← refuse w
  let outpoint : Outpoint := match tr.recipientType with
    | some (.blind o) => o
    | _ => ⟨txid, vout.toUInt32⟩
  -- room on the receiving UTXO
  let taken := match w.db.txo? outpoint with
    | some t => ((w.db.allocationsOn t).filter fun a => a.incoming && a.status != .failed).length + w.db.pendingBlinded t - 1
    | none => 0
  if taken + receiving.length > w.data.maxAllocationsPerUtxo then return ← refuse w
  -- phase 2: the paying witness is taken from the consignment
  let payingTx := (c.bundles.find? (·.witnessId == txid)).map (·.tx)
  let r := (world.chain.resolver w.chainNet).withConsignmentTxes payingTx.toList
  let status ← match pv.resolveAll r with
    | .ok pv => if !pv.pendingClaims.isEmpty then return ← refuse w else pure pv.finalize
    | .error (.invalidConsignment _) => return ← refuse w
    | .error e => throw (.network (reprStr e))
  let valid : ValidConsignment := ⟨c, status⟩
  -- record the payment
  let mut w := w
  if (w.db.asset? (toString c.contractId)).isNone then
    let (ai, db) := w.db.fresh
    w := { w with db := { db with assets := db.assets ++ [{ assetRowOf schema c.genesis now with idx := ai }] } }
  let setAsset (a : DbAssetTransfer) : DbAssetTransfer :=
    if a.idx == at_.idx then { a with assetId := some (toString c.contractId) } else a
  let db : Db := { w.db with assetTransfers := w.db.assetTransfers.map setAsset }
  let db := db.updateBatch bi fun b => { b with txid := some txid, updatedAt := now }
  let (txoIdx, db) : Nat × Db := match tr.recipientType with
    | some (.blind o) => (((db.txo? o).map (·.idx)).getD 0, db)
    | _ => db.setTxo ⟨txid, vout.toUInt32⟩ 0 (exists_ := false) (pendingWitness := true)
  let db := if (match tr.recipientType with | some (.witness _) => true | _ => false) then
      db.updateTransfer tr.idx fun t => { t with recipientType := some (.witness (some vout.toUInt32)) }
    else db
  let mut db : Db := { db with colorings := db.colorings.filter (·.assetTransferIdx != at_.idx) }
  for (opout, st) in receiving do
    let (ci, d) := db.fresh
    let col : DbColoring := ⟨ci, txoIdx, at_.idx, .receive, assignmentOf opout st⟩
    db := { d with colorings := d.colorings ++ [col] }
  let rc : Received := ⟨bi, valid.consignment⟩
  w := { w with db, inbox := (w.inbox.filter (·.batchIdx != bi)) ++ [rc] }
  -- unsafe history waits for the safe height
  let unsafeOthers := status.warnings.any fun wn => match wn with
    | .unsafeHistory l => l.any fun (_, ts) => ts.any (· != txid)
    | _ => false
  if unsafeOthers then
    return ({ w with db := w.db.updateBatch bi fun b => { b with status := .waitingSafeHeight } }, world, .waitingSafeHeight)
  -- out-of-band ACK: a witness already on chain (a donation) only waits for confirmations
  w := { w with db := w.db.updateTransfer tr.idx fun t => { t with ack := some true } }
  let st : TransferStatus := if (confirmationsOf world.chain txid).isSome then .waitingConfirmations else .waitingBroadcast
  return ({ w with db := w.db.updateBatch bi fun b => { b with status := st } }, world, st)

/-- Hand over a consignment received out of band (`provide_out_of_band_consignment`):
every pending out-of-band receive it pays is processed. -/
def provideOutOfBandConsignment (w : Wallet) (world : World) (o : Online) (c : Consignment) :
    Result (Wallet × World × List (Nat × TransferStatus)) := do
  w.checkOnline o
  let cands := w.db.batchTransfers.filter fun b =>
    b.incoming && b.status == .waitingCounterparty &&
    (w.db.assetTransfersOf b.idx).any fun at_ =>
      (at_.assetId.isNone || at_.assetId == some (toString c.contractId)) &&
      (w.db.transfersOf at_.idx).any fun t =>
        !(w.db.endpoints.any (·.transferIdx == t.idx)) &&
        (t.recipientId.bind fun r => (Beneficiary.parse r).toOption).any fun (_, b) => !(findPayments c b).isEmpty
  if cands.isEmpty then
    throw (.cannotProvideOutOfBandConsignment "no pending receive transfer matches the provided consignment")
  let mut w := w
  let mut world := world
  let mut out : List (Nat × TransferStatus) := []
  for b in cands do
    let (w', world', st) ← w.processReceived world b.idx c
    w := w'
    world := world'
    out := out ++ [(b.idx, st)]
  return (w, world, out)

/-- Complete an outgoing batch once every recipient ACKed (`try_complete_batch`):
a NACK fails it; an expired unreleased batch fails; otherwise it is broadcast. -/
def tryCompleteBatch (w : Wallet) (world : World) (bi : Nat) : Result (Wallet × World × Option TransferStatus) := do
  let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
  let trs := (w.db.assetTransfersOf bi).flatMap fun a => (w.db.transfersOf a.idx).filter (·.recipientId.isSome)
  if trs.any (·.ack == some false) then return (w.failBatch world.now bi, world, some .failed)
  if !trs.all (·.ack == some true) then return (w, world, none)
  let released := trs.all (·.ackSignature.isSome)
  if !released && (b.expiration.any (· < world.now)) then return (w.failBatch world.now bi, world, some .failed)
  let (w, world) ← w.broadcastBatch world bi
  return (w, world, some .waitingConfirmations)

/-- ACK a recipient out of band (`provide_out_of_band_ack`). -/
def provideOutOfBandAck (w : Wallet) (world : World) (o : Online) (recipientId : String) :
    Result (Wallet × World × Option Txid) := do
  w.checkOnline o
  let some tr := w.db.transfers.find? (·.recipientId == some recipientId)
    | throw (.cannotProvideOutOfBandAck "no transfer found for the provided recipient ID")
  let some b := w.db.batchOfAssetTransfer? tr.assetTransferIdx | throw (.internal "missing batch")
  if b.incoming then throw (.cannotProvideOutOfBandAck "only outgoing transfers can be ACKed")
  if b.status != .waitingCounterparty then
    throw (.cannotProvideOutOfBandAck "only WaitingCounterparty transfers can be ACKed")
  if w.db.endpoints.any fun e => e.transferIdx == tr.idx && e.kind == .recipientProxy then
    throw (.cannotProvideOutOfBandAck "recipient uses an automated transport; use refresh() to complete it instead")
  let w := { w with db := w.db.updateTransfer tr.idx fun t => { t with ack := some true } }
  let (w, world, st) ← w.tryCompleteBatch world b.idx
  match st with
  | none => return (w, world, none)
  | some .waitingConfirmations => return (w, world, b.txid)
  | some _ => throw (.cannotProvideOutOfBandAck "transfer could not be completed")

/-- Wait for confirmations (`wait_confirmations`): enough confirmations settle the
transfer; an incoming one is accepted into the stash. -/
def waitConfirmations (w : Wallet) (world : World) (b : DbBatchTransfer) : Result (Wallet × Option TransferStatus) := do
  let some txid := b.txid | return (w, none)
  match confirmationsOf world.chain txid with
  | none => return (w, none)
  | some c =>
    if c < b.minConfirmations then
      if b.status == .waitingBroadcast then
        return ({ w with db := w.db.updateBatch b.idx fun x => { x with status := .waitingConfirmations } },
          some .waitingConfirmations)
      else return (w, none)
    let mut w := w
    if b.incoming then
      if let some rc := w.inbox.find? (·.batchIdx == b.idx) then
        let schema := (AssetSchema.all.find? fun s => s.rules.schema.schemaId == rc.consignment.schemaId).getD .nia
        let r := world.chain.resolver w.chainNet
        let vc ← (rc.consignment.validate true schema.rules r { chainNet := w.chainNet }).mapError
          fun e => .consignmentValidationFailed (reprStr e)
        let stock ← (w.stock.consumeConsignment vc r).mapError fun e => .internal (reprStr e)
        w := { w with stock, inbox := w.inbox.filter (·.batchIdx != b.idx) }
      w := { w with db := { w.db with txos := w.db.txos.map fun t =>
        if t.outpoint.txid == txid then { t with pendingWitness := false, exists_ := true } else t } }
    else
      w := { w with stock := (w.stock.updateWitnesses (world.chain.resolver w.chainNet)).1 }
    return ({ w with db := w.db.updateBatch b.idx fun x => { x with status := .settled, updatedAt := world.now } },
      some .settled)

/-- Refresh every waiting transfer (`refresh`): each one independently; a failure
is reported for its batch and leaves it unchanged. -/
def refresh (w : Wallet) (world : World) (o : Online) : Result (Wallet × World × List (Nat × RefreshedTransfer)) := do
  w.checkOnline o
  let mut w := w
  let mut world := world
  let mut out : List (Nat × RefreshedTransfer) := []
  for b in w.db.batchTransfers.filter (·.status.isWaiting) do
    let step : Result (Wallet × World × Option TransferStatus) := match b.status, b.incoming with
      | .waitingCounterparty, true => .ok (w, world, none)
      | .waitingCounterparty, false => .ok (w, world, none)
      | .waitingSafeHeight, _ => .ok (w, world, none)
      | _, _ => (w.waitConfirmations world b).map fun (w', st) => (w', world, st)
    match step with
    | .ok (w', world', st) =>
      w := w'
      world := world'
      out := out ++ [(b.idx, ⟨st, none⟩)]
    | .error e => out := out ++ [(b.idx, ⟨none, some (reprStr e)⟩)]
  return (w, world, out)

/-- Fail transfers (`fail_transfers`): with an index, a fallible transfer that no
counterparty can still complete; without, every expired fallible one. -/
def failTransfers (w : Wallet) (world : World) (o : Online) (batchIdx : Option Nat := none)
    (noAssetOnly : Bool := false) : Result (Wallet × Bool) := do
  w.checkOnline o
  let now := world.now
  let hasAsset (bi : Nat) : Bool := (w.db.assetTransfersOf bi).any (·.assetId.isSome)
  let allAcked (bi : Nat) : Bool :=
    let trs := (w.db.assetTransfersOf bi).flatMap fun a => (w.db.transfersOf a.idx).filter (·.recipientId.isSome)
    !trs.isEmpty && trs.all (·.ack == some true)
  match batchIdx with
  | some bi =>
    let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
    if !b.status.isFallible then throw .cannotFailBatchTransfer
    if b.status == .waitingBroadcast && !(b.expiration.any (· < now)) then throw .cannotFailBatchTransfer
    if noAssetOnly && hasAsset bi then throw .cannotFailBatchTransfer
    if !b.incoming && b.status == .waitingCounterparty && allAcked bi then throw .cannotFailBatchTransfer
    return (w.failBatch now bi, true)
  | none =>
    let expired := w.db.batchTransfers.filter fun b =>
      b.status.isFallible && (if b.incoming then b.expiration.any (· < now)
        else b.expiration.any (· + proxyClockSkewMarginSecs < now)) &&
      !(noAssetOnly && hasAsset b.idx) && !(!b.incoming && b.status == .waitingCounterparty && allAcked b.idx)
    return (expired.foldl (fun w b => w.failBatch now b.idx) w, !expired.isEmpty)

/-- Delete failed transfers (`delete_transfers`); their colorings and the
outputs they registered but never saw go too. -/
def deleteTransfers (w : Wallet) (now : Nat) (batchIdx : Option Nat := none) (noAssetOnly : Bool := false) :
    Result (Wallet × Bool) := do
  let liveInvoice (bi : Nat) : Bool :=
    (w.db.assetTransfersOf bi).any fun a => (w.db.transfersOf a.idx).any fun t =>
      t.invoiceIdx.any fun ii => w.db.invoices.any fun inv => inv.idx == ii && now < inv.deadline
  let hasAsset (bi : Nat) : Bool := (w.db.assetTransfersOf bi).any (·.assetId.isSome)
  let targets ← match batchIdx with
    | some bi =>
      let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
      if b.status != .failed || liveInvoice bi || (noAssetOnly && hasAsset bi) then
        throw .cannotDeleteBatchTransfer
      pure [bi]
    | none => pure ((w.db.batchTransfers.filter fun b =>
        b.status == .failed && !liveInvoice b.idx && !(noAssetOnly && hasAsset b.idx)).map (·.idx))
  let db := targets.foldl (fun db bi =>
    let ats := (db.assetTransfersOf bi).map (·.idx)
    let colored := (db.colorings.filter fun c => ats.contains c.assetTransferIdx).map (·.txoIdx)
    { db with
      colorings := db.colorings.filter fun c => !ats.contains c.assetTransferIdx
      txos := db.txos.filter fun t => !(colored.contains t.idx && !t.exists_)
      transfers := db.transfers.filter fun t => !ats.contains t.assetTransferIdx
      assetTransfers := db.assetTransfers.filter fun a => a.batchTransferIdx != bi
      batchTransfers := db.batchTransfers.filter (·.idx != bi)
      reserved := db.reserved.filter (·.forColored != some bi) }) w.db
  return ({ w with db }, !targets.isEmpty)

end Wallet

end Rgb.Lib
