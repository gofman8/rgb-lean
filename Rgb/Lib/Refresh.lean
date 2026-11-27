import Rgb.Lib.Send
import Rgb.Lib.NoWallet

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

Through proxies:
* the receiver lists the transfers to its invoice on its recipient proxies, downloads the
  consignment, checks its hash and decrypts it (one that fails is refused), and keeps it with
  its metadata; a reusable invoice first discovers its transfers, giving each one after the
  first an incoming transfer of its own;
* the receiver ACKs on the sender proxy (`ack.post`), or NACKs a refused consignment. It NACKs a
  transfer whose sender proxy keeps a released transaction for less than a day. When its ACK
  completes the operation, the answer carries the signed transaction, encrypted for it: the
  receiver broadcasts it. Otherwise it posts its ACK again on each refresh until the transaction
  comes or the operation expires; a transaction not confirmed a day after the broadcast deadline
  fails the receive;
* the sender reads the ACKs on its proxy (`ack.get`), checks each signature and broadcasts once
  every recipient ACKed; a NACK fails the send. A proxy that lost the operation or serves a
  forged ACK cannot be trusted: the send completes if its transaction is on chain and fails once
  its broadcast deadline has passed;
* the receiver lets its proxy delete a handled transfer's data (`transfer.retrieved`), and
  deletes a refused transfer to a reusable invoice to free its quota slot (`transfer.delete`).

A received BFA mint comes through a proxy before its transaction is signed. The receiver checks
it like any consignment, gets the whole amount its claim locks and what the invoice asks for,
then confirms its claims (bridge locks) on the bridge's chain as of the latest finalized block.
While a lock is not confirmed the consignment waits, its locks saved; the paying mint is checked
once, assuming its lock, and saved for the receiver to make the lock. An expired lock refuses
the mint. Once the locks are confirmed the mint is accepted with no ACK and waits for the
minter's broadcast, failing only if its inputs are spent elsewhere.

A transfer that may still move cannot always be failed: `fail_transfers` first refreshes it,
then fails it only when no counterparty can still complete it; a deliberate fail of a send first
revokes its signed transaction on the sender proxy (`ack.clean`). A mint expires by its lock: a
sent one not ended fails once its lock expired, a checked received one is never failed by it.
Only failed transfers can be deleted.

Media files are not modelled.
-/

namespace Rgb.Lib

namespace Wallet

open ProxyCrypto

/-- Confirmations of a transaction; none when the chain does not know it. -/
def confirmationsOf (c : Chain) (t : Txid) : Option Nat :=
  match c.witnessOrd t with
  | .archived => none
  | _ => some (c.confirmations t)

/-- Fail a batch (`fail_batch_transfer`): drop its reservations; the outputs of an incoming
batch's witness receives stop waiting for it (`clean_failed_witness_receives`; the model flags a
receive's own output only, so the receive's script adds no output). -/
def failBatch (w : Wallet) (now bi : Nat) : Wallet :=
  let txid := (w.db.batch? bi).bind fun b => if b.incoming then b.txid else none
  let witnessOut (t : DbTransfer) : Option Outpoint :=
    match txid, t.recipientType with
    | some x, some (.witness (some v)) => some ⟨x, v⟩
    | _, _ => none
  let outs := (w.db.transfersOfBatch bi).filterMap witnessOut
  let unflag (t : DbTxo) : DbTxo :=
    if outs.contains t.outpoint then { t with pendingWitness := false } else t
  let db := w.db.updateBatch bi fun b => { b with status := .failed, updatedAt := now }
  { w with db := { db with
      reserved := db.reserved.filter (·.forColored != some bi)
      txos := db.txos.map unflag } }

/-- Set a batch's status. -/
def setStatus (w : Wallet) (bi : Nat) (st : TransferStatus) (now : Nat) : Wallet :=
  { w with db := w.db.updateBatch bi fun b => { b with status := st, updatedAt := now } }

/-- The supply a consignment issued: its genesis's and every issuance of its transitions. -/
def issuedSupplyOf (c : Consignment) : Nat :=
  let amounts (vs : Option (List RevealedData)) : Nat :=
    ((vs.getD []).filterMap fun v => match v.v with | .amount a => some a.toNat | _ => none).sum
  (c.bundles.flatMap (·.bundle.knownTransitions)).foldl
    (fun acc kt => acc + amounts (kt.transition.globals.find? Schemas.gsIssuedSupply))
    (amounts (c.genesis.globals.find? Schemas.gsIssuedSupply))

/-- An asset row from a received genesis (`extract_asset_data`). An IFA asset's known
circulating supply is `circulating`, the supply its received consignment issued, else its initial
supply. -/
def assetRowOf (schema : AssetSchema) (g : Genesis) (now : Nat) (circulating : Option Nat := none) :
    DbAsset :=
  let glob (t : GlobalStateType) : Option StrictValue := ((g.globals.find? t).bind (·.head?)).map (·.v)
  let spec := match glob Schemas.gsNominal with
    | some (.assetSpec s) => some s
    | _ => none
  let issued := match glob Schemas.gsIssuedSupply with
    | some (.amount v) => v.toNat
    | _ => if schema == .uda then 1 else 0
  let ticker := match spec, glob Schemas.gsTicker with
    | some sp, _ => some sp.ticker.s
    | none, some (.unicodeTicker t) => some t.s
    | none, _ => none
  let precision := match spec, glob Schemas.gsPrecision with
    | some sp, _ => sp.precision.decimals
    | none, some (.precision p) => p.decimals
    | none, _ => 0
  let bridgeLocation := match glob Schemas.gsBridgeLocation with
    | some (.bridgeLocation l) => some l
    | _ => none
  let details := match spec, glob Schemas.gsDetails with
    | some sp, _ => sp.details.map (·.s)
    | none, some (.details d) => some d.s
    | none, _ => none
  let maxSupply := match glob Schemas.gsMaxSupply with
    | some (.amount v) => if schema == .ifa then some v.toNat else none
    | _ => none
  let rejectList : Option RejectListLocation := match glob Schemas.gsRejectListUrl,
      glob Schemas.gsRejectList with
    | some (.rejectListUrl u), _ => some (.url u)
    | _, some (.rejectListLocation l) => some l
    | _, _ => none
  -- the model commits a linked contract as its asset id's text
  let linkedFromContract := match glob Schemas.gsLinkedFromContract with
    | some (.contractId d) => some d.data
    | _ => none
  { idx := 0, id := toString g.contractId, schema, addedAt := now
    name := (spec.map (·.name.s)).getD
      (match glob Schemas.gsName with | some (.name n) => n.s | _ => "")
    ticker, details, precision, initialSupply := if schema == .bfa then 0 else issued
    timestamp := g.timestamp, bridgeLocation, maxSupply, rejectList, linkedFromContract
    knownCirculatingSupply := if schema == .ifa then some (circulating.getD issued) else none }

/-- Where a consignment pays the receiver (`find_payments`): per bundle, each destination with
the assignments to it not spent within the consignment, dropping one with none. A blind receive's
destination is its seal; a witness receive's is each vout of the bundle's witness that a seal of
it pays at the address, with the blinding both keys derive when through a proxy, and every
assignment to that vout, whatever its blinding, is received there. -/
def findPayments (c : Consignment) (b : Beneficiary) (blinding : Option UInt64 := none) :
    List (Txid × Nat × List (Opout × AllocatedState)) :=
  let spent := c.bundles.flatMap fun wb => wb.bundle.knownTransitions.flatMap (·.transition.inputs)
  c.bundles.flatMap fun wb =>
    let tx := wb.tx
    let assigns := wb.bundle.knownTransitions.flatMap fun kt =>
      kt.transition.assignments.toList.flatMap fun (ty, ta) =>
        ta.items.zipIdx.map fun ((bs, st), no) =>
          ((⟨kt.opid, ty, no.toUInt16⟩ : Opout), bs, AllocatedState.ofRevealed st)
    -- the assignments at a destination not spent within the consignment
    let unspentAt (at_ : BuilderSeal GraphSeal → Bool) : List (Opout × AllocatedState) :=
      (assigns.filter fun (o, bs, _) => at_ bs && !spent.contains o).map fun (o, _, st) => (o, st)
    match b with
    | .blindedSeal s =>
      let r := unspentAt (·.toSecret == s)
      if r.isEmpty then [] else [(tx.txid, 0, r)]
    | .witnessVout script =>
      let pays (g : GraphSeal) : Bool := g.txptr == .witnessTx &&
        blinding.all (· == g.blinding) && (tx.outputAt? g.vout).any (·.script == script)
      let vouts := (assigns.filterMap fun (_, bs, _) =>
        (bs.revealed?.filter pays).map (·.vout.toNat)).eraseDups
      vouts.filterMap fun v =>
        let r := unspentAt fun bs =>
          bs.revealed?.any fun g => g.txptr == .witnessTx && g.vout.toNat == v
        if r.isEmpty then none else some (tx.txid, v, r)

/-! ## Mints -/

/-- `update_bfa_known_circulating_supply`: a supply read from the bridge replaces the known one. -/
def setKnownSupply (w : Wallet) (assetId : String) (supply : Option Nat) : Wallet :=
  match supply with
  | none => w
  | some s => { w with db := { w.db with assets := w.db.assets.map fun a =>
      if a.id == assetId then { a with knownCirculatingSupply := some s } else a } }

/-- `paying_mint_opid`: the mint transition of the paying bundle that created a received
allocation, for a schema with mints. -/
def payingMintOpid (schema : AssetSchema) (c : Consignment) (txid : Txid)
    (receiving : List (Opout × AllocatedState)) : Option OpId := do
  guard schema.supportsMint
  let wb ← c.bundles.find? (·.witnessId == txid)
  let kt ← wb.bundle.knownTransitions.find? fun kt =>
    kt.transition.transitionType == Schemas.tsMint && receiving.any (·.1.op == kt.opid)
  return kt.opid

/-- `mint_pays_requested`: an invoice asking for an amount is paid exactly it; one asking for any
amount, for anything or for nothing, any amount; one asking for a right, no mint. -/
def mintPaysRequested (requested : Option Assignment) (received : Nat) : Bool :=
  match requested with
  | some (.fungible r) => r == 0 || r.toNat == received
  | some .any | none => true
  | some _ => false

/-- The mint transition of a fascia's bundle of a contract. -/
def mintOpid? (f : Fascia) (cid : ContractId) : Option OpId :=
  ((f.bundles.find? cid).bind fun b =>
    b.knownTransitions.find? (·.transition.transitionType == Schemas.tsMint)).map (·.opid)

/-- `sent_mint`: the mint of a prepared operation as its sender knows it. -/
def sentMint (w : Wallet) (op : PendingOp) : Result Evm.SentMint := do
  let some beforeBlock := op.beforeBlock | throw (.internal "not a mint transfer")
  let some (assetId, lrs) := op.recipients.head? | throw (.internal "not a mint transfer")
  let some cid := w.contractIdOf? assetId | throw (.assetNotFound assetId)
  let some f := op.fascia | throw (.internal "missing fascia")
  let some opid := mintOpid? f cid | throw (.internal "mint transition missing from fascia")
  let some g := w.stock.genesis? cid | throw (.assetNotFound assetId)
  let bridgeLocation ← (NoWallet.bridgeLocation g).mapError (.internal ·)
  let amount := ((lrs.map fun (lr : LocalRecipient) => lr.assignment.mainAmount).sum).toUInt64
  return { contractId := cid, opid, lockId := LockId.of opid f.witnessId, amount, beforeBlock
           bridgeLocation }

/-- `is_pending_mint`: an outgoing mint not ended yet. -/
def isPendingMint (w : Wallet) (b : DbBatchTransfer) : Bool :=
  !b.incoming && b.status == .initiated && b.txid.isSome &&
    (w.db.assetTransfersOf b.idx).any (·.transitionType == some .mint)

/-- `is_mint`: a sent mint not ended yet, or a received mint the wallet checked. -/
def isMint (w : Wallet) (b : DbBatchTransfer) : Bool :=
  if !b.incoming then w.isPendingMint b
  else match w.db.incomingTransfer? b.idx with
    | some (_, tr) => tr.recipientId.isSome && (w.receivedMints.lookup tr.idx).isSome
    | none => false

/-- `received_mint_tx_inputs_spent_elsewhere`: a confirmed transaction spends an input of the
mint's transaction, which is not that transaction confirmed. -/
def receivedMintTxInputsSpentElsewhere (w : Wallet) (b : DbBatchTransfer) (c : Chain) : Bool :=
  match b.txid, w.inbox.find? (·.batchIdx == b.idx) with
  | some t, some rc =>
    match rc.consignment.bundles.find? (·.witnessId == t) with
    | some wb =>
      wb.tx.inputs.any (fun i => c.minedTxs.any fun (x, _) => x.spends i.prevout) &&
        (confirmationsOf c t).all (· == 0)
    | none => false
  | _, _ => false

/-- `fail_expired_mint`: a sent mint not ended yet whose lock expired is failed, releasing its
inputs; one whose lock is confirmed or may still be is not. -/
def failExpiredMint (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Bool) := do
  let world ← get
  let some t := b.txid | throw (.internal "a pending mint has a TXID")
  let some op := w.pending.find? (·.txid == t) | throw (.unknownTransfer (toString t))
  let m ← Net.ofResult (w.sentMint op)
  match Evm.checkMintLock world.evmNet w.evmRpcUrls m with
  | .error (.mintLockExpired ..) => return (w.failBatch world.now b.idx, true)
  | .ok _ | .error (.mintLockNotFound _) => return (w, false)
  | .error e => throw e

/-! ## Receiving -/

/-- A transfer downloaded from a recipient proxy (`ProxyReceiveData`). -/
structure ProxyReceiveData where
  proxyUrl : String
  transferId : String
  /-- HTTP URL of the sender proxy. -/
  senderProxy : String
  senderPubkey : String
  consignmentHash : String
  recipientEncryption : Encryption
  batch : Bool
  deriving DecidableEq, Repr, Inhabited

/-- How a receive got its consignment (`ReceiveMode`). -/
inductive ReceiveMode where
  | outOfBand
  | proxy (d : ProxyReceiveData)
  deriving DecidableEq, Repr, Inhabited

/-- The wallet's files in the world. -/
def files (w : Wallet) : Net WalletFiles := do return (← get).filesOf w.fingerprint

/-- Change the wallet's files in the world: the change stays when the step fails afterwards. -/
def modifyFiles (w : Wallet) (f : WalletFiles → WalletFiles) : Net Unit :=
  modify fun world => world.setFiles w.fingerprint (f (world.filesOf w.fingerprint))

/-- What a recipient saves of a downloaded transfer (`record_received_consignment`): its rows,
and the consignment with its metadata in its files. -/
def recordReceived (w : Wallet) (tr : DbTransfer) (d : ProxyReceiveData) (file : Payload) :
    Net Wallet := do
  let info : ReceivedInfo :=
    { proxyUrl := some d.proxyUrl, transferId := some d.transferId
      senderTransportEndpoint := d.senderProxy, senderPubkey := d.senderPubkey
      consignmentHash := d.consignmentHash, batch := d.batch }
  w.modifyFiles fun f =>
    { f with downloads := (f.downloads.filter (·.1 != tr.idx)) ++ [(tr.idx, ⟨file, info⟩)] }
  let db := w.db.updateTransfer tr.idx fun t =>
    { t with consignmentHash := some d.consignmentHash, proxyTransferId := some d.transferId }
  return { w with db := db.saveSenderProxy tr.idx d.senderProxy }

/-- `release_handled_transfer`: once a downloaded transfer is ACKed or refused, its recipient
proxy may drop its data; a refused transfer to a reusable invoice is deleted, freeing its slot. -/
def releaseHandled (tr : DbTransfer) (d : ProxyReceiveData) (recipient : SecretKey)
    (st : Option TransferStatus) : Net Unit := do
  let some s := st | return
  let delete := tr.invoiceIdx.isSome && s == .failed
  ProxyClient.releaseTransferData d.proxyUrl d.transferId recipient delete

/-- `refuse_consignment`: through a proxy a NACK is posted first, unless the consignment is a
mint (an ACK already recorded, or no operation on the sender proxy, does not stop the refusal;
any other error does); then the receive fails, its valid copy goes, and an output of its witness
stops waiting for it unless its script is shared with other receives. -/
def refuseConsignment (w : Wallet) (b : DbBatchTransfer) (tr : DbTransfer) (mode : ReceiveMode)
    (mint : Bool := false) : Net (Wallet × Option TransferStatus) := do
  let now ← Net.now
  if let .proxy d := mode then
    if !mint then
      let recipient : SecretKey := ⟨b.operationSecretKey.getD ""⟩
      let nack := ProxyClient.signAndPostAck d.senderProxy d.transferId false d.consignmentHash
      match ← Net.attempt (nack recipient) with
      | .ok _ | .error (.proxyCannotChange _) | .error .operationNotFound => pure ()
      | .error e => throw e
  let txid := (w.db.batch? b.idx).bind (·.txid)
  let db := w.db.updateBatch b.idx fun x => { x with status := .failed, updatedAt := now }
  let unflag (t : DbTxo) : DbTxo :=
    if tr.receiveDir.isNone && txid == some t.outpoint.txid then { t with pendingWitness := false }
    else t
  let db := { db with txos := db.txos.map unflag }
  return ({ w with db, inbox := w.inbox.filter (·.batchIdx != b.idx) }, some .failed)

/-- `broadcast_received_tx`: decrypt the released transaction with the key shared with the
sender the answer names, check its hash, keep it (`rcv_signed.tx`) and broadcast it. -/
def broadcastReceivedTx (w : Wallet) (tr : DbTransfer) (blob : Blob) (hash senderPk : String)
    (recipient : SecretKey) : Net Wallet := do
  if !isPubkeyHex senderPk then throw (.internal "invalid counterparty pubkey")
  let p ← Net.ofResult (blob.decryptWith .required (deriveShared recipient senderPk).symKey hash)
  -- the model's stand-in for the consensus decoding error
  let some tx := p.tx? | throw (.internal "invalid signed transaction")
  w.modifyFiles fun f =>
    { f with releasedTxs := (f.releasedTxs.filter (·.1 != tr.idx)) ++ [(tr.idx, tx)] }
  broadcastTx tx
  return w

/-- `ack_consignment`: ACK a valid consignment. Through a proxy, unless it is a donation or a
mint, the sender proxy must keep a released transaction for at least a day, else the transfer is
NACKed; the ACK answer gives the broadcast deadline and, once released, the signed transaction,
which is broadcast. A donation's transaction travels in its consignment: it is broadcast at once.
A mint is posted before its transaction is signed: nothing is ACKed, the minter broadcasts. -/
def ackConsignment (w : Wallet) (b : DbBatchTransfer) (tr : DbTransfer) (mode : ReceiveMode)
    (donation : Option Tx) (mint : Bool := false) : Net (Wallet × Option TransferStatus) := do
  let now ← Net.now
  let recipient : SecretKey := ⟨b.operationSecretKey.getD ""⟩
  let mut grace : Option Nat := none
  if let .proxy d := mode then
    if donation.isNone && !mint then
      let g ← ProxyClient.senderRetentionGrace d.senderProxy
      if g < minSenderRetentionGraceSecs then return ← w.refuseConsignment b tr mode
      grace := some g
  -- `record_own_ack`, once the ACK is accepted or not needed
  let acked := { w with db := w.db.updateTransfer tr.idx fun t => { t with ack := some true } }
  match mode with
  | .outOfBand =>
    if let some tx := donation then
      broadcastTx tx
      return (acked.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
    return (acked.setStatus b.idx .waitingBroadcast now, some .waitingBroadcast)
  | .proxy d =>
    if mint then return (acked.setStatus b.idx .waitingBroadcast now, some .waitingBroadcast)
    let ack := ProxyClient.signAndPostAck d.senderProxy d.transferId true d.consignmentHash
    match ← Net.attempt (ack recipient) with
    | .error .operationNotFound =>
      let some tx := donation | throw .operationNotFound
      broadcastTx tx
      return (acked.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
    | .error (.proxyCannotChange _) => return (w.failBatch now b.idx, some .failed)
    | .error e => throw e
    | .ok res =>
      let mut w := acked
      if let some g := grace then
        let deadline := ProxyClient.broadcastDeadline res.expiresAt g b.expiration now
        w := { w with db := w.db.updateBatch b.idx fun x =>
          { x with broadcastDeadline := deadline } }
      match res.signedTx, res.signedTxHash, res.senderPk with
      | some blob, some hash, some senderPk =>
        let w2 ← w.broadcastReceivedTx tr blob hash senderPk recipient
        return (w2.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
      | _, _, _ =>
        if let some tx := donation then
          broadcastTx tx
          return (w.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
        return (w.setStatus b.idx .waitingBroadcast now, some .waitingBroadcast)

/-- What the claims of a received consignment decide. -/
inductive ClaimsStep where
  /-- The consignment waits: its locks are saved, or no usable endpoint reaches the bridge. -/
  | wait (w : Wallet)
  /-- The consignment is refused; `mint` once it is known to be a mint. -/
  | refuse (mint : Bool)
  /-- Every claim is confirmed: the claims resolved, the paying mint, the bridge's supply. -/
  | confirmed (pv : PendingValidation) (mint : Option Evm.ReceivedMint) (supply : Option Nat)

/-- The claims (bridge mint locks) of a received consignment `file` for the receive `tr`,
confirmed on the chain of the asset's `bridge` as of its latest finalized block
(`process_received_consignment`).
An expired lock refuses the consignment. While some are not confirmed the consignment waits, the
locks saved with the digest of its file. The paying mint is checked once, after the other mints
it relies on, assuming its lock: refused when its lock is not recorded and its block is too far,
or when invalid; else saved, and from then on it is waited for until its lock is confirmed or
expired. A missing or misconfigured EVM endpoint makes it wait. -/
def resolveReceivedClaims (w : Wallet) (tr : DbTransfer) (file : Payload) (bridge : EvmContract)
    (pv : PendingValidation) (claims : List Claim) (payingClaim : Option Claim) (checked : Bool)
    (r : Resolver) : Net ClaimsStep := do
  let world ← get
  let chainId := bridge.chainId.toNat
  let receivedMint : Option Evm.ReceivedMint := payingClaim.map fun cl =>
    { opid := toString cl.opid, lockId := cl.lockId, amount := cl.amount.toNat
      beforeBlock := cl.beforeBlock.toNat, evmChainId := chainId
      bridgeContract := Evm.addressText bridge.address }
  let some url := w.evmRpcUrls.lookup chainId | return .wait w
  let node := world.evmNet url
  let checkedResolver := Evm.CheckedClaimResolver.check (Evm.mintClaimResolver node) (.evm bridge)
  let resolver ← match checkedResolver with
    | .ok x => pure x
    | .error (.wrongChainId ..) => return .wait w
    | .error e => throw e.toError
  let (pv, unconfirmed) ← match NoWallet.resolveClaims pv resolver claims with
    | .ok x => pure x
    | .error (.mintLockExpired ..) => return .refuse receivedMint.isSome
    | .error e => throw e
  let payingOpid := payingClaim.map (·.opid)
  let mut committed := checked || payingOpid.any (!unconfirmed.contains ·)
  if unconfirmed.isEmpty then
    return .confirmed pv receivedMint (Evm.readCirculatingSupply node bridge.address)
  -- an unchecked mint waits for the other mints it relies on first
  let others := unconfirmed.any (some · != payingOpid)
  let waitingFor := if receivedMint.isSome && !checked && others then
      unconfirmed.filter (some · != payingOpid)
    else unconfirmed
  let mut w := w
  if let (some rm, some pc) := (receivedMint, payingClaim) then
    if !checked && !others then
      if !committed then
        committed ← Net.ofResult
          (node.mintLockRecorded bridge.address pc.lockId pc.amount rm.beforeBlock)
      if !committed then
        let some chain := w.evmChains.lookup chainId | throw (.internal "missing EVM chain")
        let latest ← Net.ofResult node.blockNumber
        if Evm.receivedMintTooFar committed rm.beforeBlock latest chain.maxMintLockBlocks then
          return .refuse true
      let assume (p : PendingValidation) (cl : Claim) := p.resolveClaim cl
      let assumed ← Net.ofResult ((claims.foldlM assume pv).mapError fun e =>
        .internal s!"unexpected claim resolution error: {reprStr e}")
      match assumed.resolveAll r with
      | .ok _ => pure ()
      | .error (.invalidConsignment _) => return .refuse true
      | .error e => throw (.network (reprStr e))
      -- a backup older than the check misses it
      let info := { w.db.backupInfo with lastOperationTimestamp := world.now }
      w := { w with receivedMints := (w.receivedMints.filter (·.1 != tr.idx)) ++ [(tr.idx, rm)]
                    db := { w.db with backupInfo := info } }
  let saved : Evm.PendingMintLocks :=
    { consignmentDigest := file.hash, evmChainId := chainId, bridgeContract := bridge.address
      claims := claims.filter (waitingFor.contains ·.opid) }
  return .wait { w with mintLocks := (w.mintLocks.filter (·.1 != tr.idx)) ++ [(tr.idx, saved)] }

/-- Accept or refuse a consignment received for an incoming batch
(`process_received_consignment`); `file` is the received file, which must be a consignment.
Through a proxy a witness payment must carry the derived blinding. A paying witness already on
chain counts as a donation (the model's transactions carry no signatures). A mint paying the
receiver is refused unless the wallet accepts mints, it came through a proxy, and the receiver
gets the whole amount of its claim and the amount its invoice asks for; claims are then resolved
(`resolveReceivedClaims`). Reject lists are not checked. -/
def processReceived (w : Wallet) (b : DbBatchTransfer) (file : Payload) (mode : ReceiveMode) :
    Net (Wallet × Option TransferStatus) := do
  let world ← get
  let now := world.now
  let bi := b.idx
  let some at_ := (w.db.assetTransfersOf bi).head? | throw (.internal "missing asset transfer")
  let some tr := (w.db.transfersOf at_.idx).head? | throw (.internal "missing transfer")
  let checked := (w.receivedMints.lookup tr.idx).isSome
  let refuse (mint : Bool) := w.refuseConsignment b tr mode (mint || checked)
  -- a consignment waiting for its mint locks was validated as far as it can be without them
  let saved := w.mintLocks.lookup tr.idx
  if (← Net.ofResult (Evm.waitingForMintLocks world.evmNet w.evmRpcUrls saved file.hash)) then
    return (w, none)
  let some c := file.consignment? | return ← refuse false
  let some schema := AssetSchema.ofSchemaId? c.schemaId
    | throw (.unknownRgbSchema (toString c.schemaId))
  if !w.data.supportedSchemas.contains schema then return ← refuse false
  if let some id := at_.assetId then
    if id != toString c.contractId then return ← refuse false
  let mut blinding : Option UInt64 := none
  if let .proxy d := mode then
    match ProxyClient.sealBlinding ⟨b.operationSecretKey.getD ""⟩ d.senderPubkey with
    | some x => blinding := some x
    | none => return ← refuse false
  let some rid := tr.recipientId | throw (.internal "missing recipient id")
  let (_, beneficiary) ← Net.ofResult (Beneficiary.parse rid)
  let tip := world.chain.height
  let safeHeight := tip + 1 - min b.minConfirmations tip
  let cfg : ValidationConfig := { chainNet := w.chainNet, safeHeight := some safeHeight }
  let pv ← match c.validateDeterministic true schema.rules cfg with
    | .ok pv => pure pv
    | .error (.invalidConsignment _) => return ← refuse false
    | .error e => throw (.consignmentValidationFailed (reprStr e))
  -- `pending_claims`: claims need a schema with mints, and live on the chain of its bridge
  let claims := NoWallet.unresolvedClaims pv
  if !claims.isEmpty && !schema.supportsMint then return ← refuse false
  let bridge ← if claims.isEmpty then pure none else
    match NoWallet.bridgeLocation c.genesis with
    | .ok (.evm b) => pure (some b)
    | .error e => throw (.internal s!"unexpected bridge location error: {e}")
  let payments := findPayments c beneficiary blinding
  if payments.length != 1 then return ← refuse false
  let (txid, vout, receiving) := payments.headD default
  -- already received with the same transaction, at the same output for a witness receive
  let paidVout := match tr.recipientType with
    | some (.witness _) => some vout.toUInt32
    | _ => none
  let dup := w.db.transfers.any fun t => t.idx != tr.idx && t.recipientId == some rid &&
    (w.db.batchOfAssetTransfer? t.assetTransferIdx).any (fun b =>
      b.incoming && b.status != .failed && b.txid == some txid) &&
    (match t.recipientType with | some (.witness v) => v == paidVout | _ => true)
  if dup then return ← refuse false
  if receiving.length != 1 then return ← refuse false
  -- a mint paying the receiver is refused before it is checked, so that no lock is made for it
  let received := (receiving.map fun (o, st) => (assignmentOf o st).mainAmount).sum
  let mut payingClaim : Option Claim := none
  if let some opid := payingMintOpid schema c txid receiving then
    if !w.acceptsReceivedMints || mode == .outOfBand then return ← refuse false
    let claim := claims.find? (·.opid == opid)
    if claim.map (·.amount.toNat) != some received || receiving.any (·.1.op != opid) then
      return ← refuse false
    if !mintPaysRequested tr.requestedAssignment received then return ← refuse false
    payingClaim := claim
  let outpoint : Outpoint := match tr.recipientType with
    | some (.blind o) => o
    | _ => ⟨txid, vout.toUInt32⟩
  -- room on the receiving UTXO: its allocations that did not fail, its other unpaid invoices
  let taken := match w.db.txo? outpoint with
    | some t =>
      if t.spent then 0 else
      (w.db.colorings.filter fun col => col.txoIdx == t.idx && col.type.isIncoming &&
        col.assetTransferIdx != at_.idx &&
        (w.db.batchOfAssetTransfer? col.assetTransferIdx).any (·.status != .failed)).length +
      ((w.db.unpaidInvoices outpoint).filter (·.idx != tr.idx)).length
    | none => 0
  if taken + receiving.length > w.data.maxAllocationsPerUtxo then return ← refuse false
  -- the paying witness is taken from the consignment
  let payingTx := (c.bundles.find? (·.witnessId == txid)).map (·.tx)
  let r := NoWallet.offchainResolver c (some txid) (world.chain.resolver w.chainNet)
  let mut pv := pv
  let mut receivedMint : Option Evm.ReceivedMint := none
  let mut supply : Option Nat := none
  if let some bridge := bridge then
    match ← w.resolveReceivedClaims tr file bridge pv claims payingClaim checked r with
    | .wait w' => return (w', none)
    | .refuse mint => return ← refuse mint
    | .confirmed pv' rm s =>
      pv := pv'
      receivedMint := rm
      supply := s
  -- phase 2
  let status ← match pv.resolveAll r with
    | .ok p => pure p.finalize
    | .error (.invalidConsignment _) => return ← refuse receivedMint.isSome
    | .error e => throw (.network (reprStr e))
  -- record the payment
  let mut w := w
  if let some rm := receivedMint then
    w := { w with receivedMints := (w.receivedMints.filter (·.1 != tr.idx)) ++ [(tr.idx, rm)] }
  if (w.db.asset? (toString c.contractId)).isNone then
    let (ai, db) := w.db.fresh
    let row := { assetRowOf schema c.genesis now (some (issuedSupplyOf c)) with idx := ai }
    w := { w with db := { db with assets := db.assets ++ [row] } }
  w := w.setKnownSupply (toString c.contractId) supply
  let setAsset (a : DbAssetTransfer) : DbAssetTransfer :=
    if a.idx == at_.idx then { a with assetId := some (toString c.contractId) } else a
  let db : Db := { w.db with assetTransfers := w.db.assetTransfers.map setAsset }
  let db := db.updateBatch bi fun b => { b with txid := some txid, updatedAt := now }
  let (txoIdx, db) : Nat × Db := match tr.recipientType with
    | some (.blind o) => (((db.txo? o).map (·.idx)).getD 0, db)
    | _ => db.setTxo ⟨txid, vout.toUInt32⟩ 0 (exists_ := false) (pendingWitness := true)
  let db := if (match tr.recipientType with | some (.witness _) => true | _ => false) then
      db.updateTransfer tr.idx fun t =>
        { t with recipientType := some (.witness (some vout.toUInt32)) }
    else db
  let mut db : Db := { db with colorings := db.colorings.filter (·.assetTransferIdx != at_.idx) }
  for (opout, st) in receiving do
    let (ci, d) := db.fresh
    let col : DbColoring := ⟨ci, txoIdx, at_.idx, .receive, assignmentOf opout st⟩
    db := { d with colorings := d.colorings ++ [col] }
  let rc : Received := ⟨bi, c, status⟩
  w := { w with db, inbox := (w.inbox.filter (·.batchIdx != bi)) ++ [rc] }
  -- unsafe history waits for the safe height
  let unsafeOthers := status.warnings.any fun wn => match wn with
    | .unsafeHistory l => l.any fun (_, ts) => ts.any (· != txid)
    | _ => false
  if unsafeOthers then
    return (w.setStatus bi .waitingSafeHeight now, some .waitingSafeHeight)
  let donation := if (confirmationsOf world.chain txid).isSome then payingTx else none
  w.ackConsignment b tr mode donation (mint := payingClaim.isSome)

/-- Hand over a consignment received out of band (`provide_out_of_band_consignment`):
every pending out-of-band receive it pays is processed, reported as `refresh` reports it. -/
def provideOutOfBandConsignment (w : Wallet) (world : World) (o : Online) (c : Consignment) :
    Result (Wallet × World × List (Nat × RefreshedTransfer)) := do
  w.checkOnline o
  let now := world.now
  let cands := w.db.batchTransfers.filter fun b =>
    b.incoming && b.status == .waitingCounterparty &&
    (w.db.assetTransfersOf b.idx).any fun at_ =>
      (at_.assetId.isNone || at_.assetId == some (toString c.contractId)) &&
      (w.db.transfersOf at_.idx).any fun t =>
        w.db.usesOutOfBand t &&
        (t.recipientId.bind fun r => (Beneficiary.parse r).toOption).any fun (_, b) => !(findPayments c b).isEmpty
  if cands.isEmpty then
    throw (.cannotProvideOutOfBandConsignment "no pending receive transfer matches the provided consignment")
  let step : Net (Wallet × List (Nat × RefreshedTransfer)) := do
    let mut w := w
    let mut out : List (Nat × RefreshedTransfer) := []
    for b in cands do
      let (w', st) ← w.processReceived b (.consignment c) .outOfBand
      w := w'
      out := out ++ [(b.idx, ⟨st, none⟩)]
    return (w, out)
  let (r, world) := step.exec world
  let (w, out) ← r
  return (w.updateBackupInfo now, world, out)

/-- `save_received_consignment`: decrypt a downloaded consignment, check its hash and keep it
with its metadata; one that fails is refused, and its proxy may drop it. -/
def saveReceivedConsignment (w : Wallet) (b : DbBatchTransfer) (tr : DbTransfer) (url tid : String)
    (res : Proxy.ConsignmentGetResult) :
    Net (Sum (Wallet × ProxyReceiveData × Payload) (Wallet × Option TransferStatus)) := do
  let recipient : SecretKey := ⟨b.operationSecretKey.getD ""⟩
  let senderProxy := (← Net.ofResult (TransportEndpoint.new res.senderTransportEndpoint)).endpoint
  let d : ProxyReceiveData :=
    { proxyUrl := url, transferId := tid, senderProxy, senderPubkey := res.senderPk
      consignmentHash := res.consignmentHash, recipientEncryption := tr.recipientEncryption
      batch := res.batch }
  let key := (deriveShared recipient res.senderPk).symKey
  let file := if isPubkeyHex res.senderPk then
      (res.consignment.decryptWith tr.recipientEncryption key res.consignmentHash).toOption
    else none
  match file with
  | some p => return .inl (← w.recordReceived tr d p, d, p)
  | none =>
    let r ← w.refuseConsignment b tr (.proxy d)
    releaseHandled tr d recipient r.2
    return .inr r

/-- `wait_consignment`: find the transfer to the invoice on the recipient proxies (one downloaded
before, kept in the files a failed step leaves, is reused), download and save its consignment,
then process it; a handled transfer is released on its proxy. A transfer of a reusable invoice
waits until discovery assigns it. -/
def waitConsignment (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Option TransferStatus) := do
  let some (_, tr) := w.db.incomingTransfer? b.idx | throw (.internal "missing transfer")
  if w.db.usesOutOfBand tr then return (w, none)
  let recipient : SecretKey := ⟨b.operationSecretKey.getD ""⟩
  let ttes := w.db.recipientProxiesOf tr.idx
  let fs ← w.files
  let cached := (fs.downloads.lookup tr.idx).bind fun dl => dl.info.transferId.bind fun tid =>
    let matching (e : DbTransferEndpoint) : Bool := match dl.info.proxyUrl with
      | some u => u == e.endpoint
      | none => e.used
    (ttes.find? matching).map (dl, tid, ·)
  let mut w := w
  let mut data : ProxyReceiveData := default
  let mut file : Payload := default
  match cached with
  | some (dl, tid, e) =>
    data := { proxyUrl := e.endpoint, transferId := tid
              senderProxy := dl.info.senderTransportEndpoint, senderPubkey := dl.info.senderPubkey
              consignmentHash := dl.info.consignmentHash
              recipientEncryption := tr.recipientEncryption, batch := dl.info.batch }
    file := dl.file
    let db := w.db.setEndpointUsed tr.idx e.endpoint true
    let db := if tr.consignmentHash.isNone || tr.proxyTransferId.isNone then
        db.updateTransfer tr.idx fun t =>
          { t with consignmentHash := some dl.info.consignmentHash, proxyTransferId := some tid }
      else db
    w := { w with db := db.saveSenderProxy tr.idx dl.info.senderTransportEndpoint }
  | none =>
    let some pk := tr.recipientPubkey | throw (.internal "missing recipient pubkey")
    let some rid := tr.recipientId | throw (.internal "missing recipient id")
    let iid := invoiceId rid pk
    if tr.invoiceIdx.isSome && tr.proxyTransferId.isNone then return (w, none)
    let mut found : Option (String × String × Proxy.ConsignmentGetResult) := none
    for e in ttes do
      let r ← match tr.proxyTransferId with
        | some tid =>
          if e.used then (·.map (tid, ·)) <$> ProxyClient.fetchInvoiceTransfer e.endpoint iid tid
          else pure none
        | none => ProxyClient.findInvoiceTransfer e.endpoint iid recipient
      if let some (tid, res) := r then
        found := some (e.endpoint, tid, res)
        break
    let some (url, tid, res) := found | return (w, none)
    w := { w with db := w.db.setEndpointUsed tr.idx url true }
    match ← w.saveReceivedConsignment b tr url tid res with
    | .inl (w', d, p) =>
      w := w'
      data := d
      file := p
    | .inr r => return r
  let r ← w.processReceived b file (.proxy data)
  releaseHandled tr data recipient r.2
  return r

/-- `wait_safe_height`: once the witnesses its validation flagged as unsafe history, other than
the paying one, are mined at or below the safe height, ACK as after validation, through the proxy
the consignment came from. -/
def waitSafeHeight (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Option TransferStatus) := do
  let world ← get
  let some (_, tr) := w.db.incomingTransfer? b.idx | throw (.internal "missing transfer")
  let some txid := b.txid | return (w, none)
  if b.isLegacy then
    if (confirmationsOf world.chain txid).isSome then
      return (w.setStatus b.idx .waitingConfirmations world.now, some .waitingConfirmations)
    return (w.failBatch world.now b.idx, some .failed)
  let some rc := w.inbox.find? (·.batchIdx == b.idx) | return (w, none)
  let tip := world.chain.height
  let safe := tip + 1 - min b.minConfirmations tip
  let unsafeTxids := (rc.status.warnings.flatMap fun wn => match wn with
    | .unsafeHistory l => l.flatMap (·.2)
    | _ => []).filter (· != txid)
  let notSafe := unsafeTxids.any fun t => match world.chain.witnessOrd t with
    | .mined p => p.height > safe
    | _ => true
  if notSafe then return (w, none)
  let payingTx := (rc.consignment.bundles.find? (·.witnessId == txid)).map (·.tx)
  let donation := if (confirmationsOf world.chain txid).isSome then payingTx else none
  let mode ← if (w.db.endpointsOf tr.idx).isEmpty then pure ReceiveMode.outOfBand else do
    let some e := (w.db.recipientProxiesOf tr.idx).find? (·.used)
      | throw (.internal "there should be 1 used transport endpoint")
    let some dl := (← w.files).downloads.lookup tr.idx
      | throw (.internal "missing consignment metadata")
    let some tid := tr.proxyTransferId <|> dl.info.transferId
      | throw (.internal "missing transfer ID")
    pure (.proxy { proxyUrl := e.endpoint, transferId := tid
                   senderProxy := dl.info.senderTransportEndpoint
                   senderPubkey := dl.info.senderPubkey, consignmentHash := dl.info.consignmentHash
                   recipientEncryption := tr.recipientEncryption, batch := dl.info.batch })
  w.ackConsignment b tr mode donation (mint := (w.receivedMints.lookup tr.idx).isSome)

/-- Wait for confirmations (`wait_confirmations`): enough confirmations settle the
transfer; an incoming one is accepted into the stash, raising an IFA asset's known circulating
supply to what the stash knows was issued. An incoming transfer with a broadcast deadline whose
transaction is not confirmed fails a day after the deadline; before the deadline a released
transaction missing from the chain is broadcast again (a failure is only logged). -/
def waitConfirmations (w : Wallet) (b : DbBatchTransfer) :
    Net (Wallet × Option TransferStatus) := do
  let some txid := b.txid | return (w, none)
  let world ← get
  let now := world.now
  let conf := confirmationsOf world.chain txid
  if b.incoming && b.broadcastDeadline.isSome && conf.getD 0 == 0 then
    if b.confirmationDeadlinePassed now then return (w.failBatch now b.idx, some .failed)
    if conf.isNone && b.broadcastDeadline.any (now ≤ ·) then
      if let some (_, tr) := w.db.incomingTransfer? b.idx then
        if let some tx := (← w.files).releasedTxs.lookup tr.idx then
          discard (Net.attempt (broadcastTx tx))
  let world ← get
  match conf with
  | none => return (w, none)
  | some c =>
    if c < b.minConfirmations then
      if b.status == .waitingBroadcast then
        return (w.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
      else return (w, none)
    let mut w := w
    if b.incoming then
      -- the validated copy kept since the consignment was accepted
      if let some rc := w.inbox.find? (·.batchIdx == b.idx) then
        let r := world.chain.resolver w.chainNet
        let vc : ValidConsignment := ⟨rc.consignment, rc.status⟩
        let stock ← Net.ofResult ((w.stock.consumeConsignment vc r).mapError
          fun e => .internal (reprStr e))
        w := { w with stock, inbox := w.inbox.filter (·.batchIdx != b.idx) }
        let cid := rc.consignment.contractId
        if AssetSchema.ofSchemaId? rc.consignment.schemaId == some .ifa then
          let issued := ((stock.globalValues cid Schemas.gsIssuedSupply).filterMap fun v =>
            match v.v with | .amount a => some a.toNat | _ => none).sum
          let raise (a : DbAsset) : DbAsset :=
            if a.id == toString cid && a.knownCirculatingSupply.getD a.initialSupply < issued then
              { a with knownCirculatingSupply := some issued }
            else a
          w := { w with db := { w.db with assets := w.db.assets.map raise } }
      let settle (t : DbTxo) : DbTxo :=
        if t.outpoint.txid == txid then { t with pendingWitness := false, exists_ := true } else t
      w := { w with db := { w.db with txos := w.db.txos.map settle } }
    else
      w := { w with stock := (w.stock.updateWitnesses (world.chain.resolver w.chainNet)).1 }
    return (w.setStatus b.idx .settled now, some .settled)

/-- `wait_broadcast`: a proxy recipient that ACKed posts its ACK again until the sender proxy
releases the signed transaction, which it broadcasts. An expired operation fails the transfer; a
proxy that lost the operation or gives no answer fails it a day after the broadcast deadline. A
received mint waits for the minter's broadcast, failing once its inputs are spent elsewhere. -/
def waitBroadcast (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Option TransferStatus) := do
  let now ← Net.now
  let some (_, tr) := w.db.incomingTransfer? b.idx | throw (.internal "missing transfer")
  if b.isLegacy then
    return if b.isExpired now then (w.failBatch now b.idx, some .failed) else (w, none)
  if w.isMint b then
    if w.receivedMintTxInputsSpentElsewhere b (← get).chain then
      return (w.failBatch now b.idx, some .failed)
    return (w, none)
  let some url := w.db.senderProxyOf? tr.idx | return (w, none)
  let some ch := tr.consignmentHash | throw (.internal "missing consignment hash")
  let recipient : SecretKey := ⟨b.operationSecretKey.getD ""⟩
  let some tid := tr.proxyTransferId | throw (.internal "missing transfer ID")
  let failIfPast : Wallet × Option TransferStatus :=
    if b.confirmationDeadlinePassed now then (w.failBatch now b.idx, some .failed) else (w, none)
  match ← Net.attempt (ProxyClient.signAndPostAck url tid true ch recipient) with
  | .error .operationExpired => return (w.failBatch now b.idx, some .failed)
  | .error .operationNotFound => return failIfPast
  | .error e => if failIfPast.2.isSome then return failIfPast else throw e
  | .ok res =>
    let mut w := w
    let mut deadlineChanged := false
    if b.broadcastDeadline.isNone then
      let grace ← ProxyClient.senderRetentionGrace url
      if let some d := ProxyClient.broadcastDeadline res.expiresAt grace b.expiration now then
        w := { w with db := w.db.updateBatch b.idx fun x => { x with broadcastDeadline := some d } }
        deadlineChanged := true
    match res.signedTx, res.signedTxHash, res.senderPk with
    | some blob, some hash, some senderPk =>
      let w2 ← w.broadcastReceivedTx tr blob hash senderPk recipient
      return (w2.setStatus b.idx .waitingConfirmations now, some .waitingConfirmations)
    | _, _, _ => return if deadlineChanged then (w, none) else failIfPast

/-! ## Sending -/

/-- `tx_inputs_spent_elsewhere`: a confirmed transaction other than the operation's spends one
of its inputs, so it can never confirm. -/
def txInputsSpentElsewhere (w : Wallet) (b : DbBatchTransfer) (c : Chain) : Bool :=
  match b.txid.bind fun t => w.pending.find? (·.txid == t) with
  | none => false
  | some op => op.tx.inputs.any fun i =>
    c.minedTxs.any fun (x, _) => x.txid != op.txid && x.spends i.prevout

/-- `complete_batch_if_tx_on_chain`: an outgoing operation whose transaction a recipient
broadcast is completed. -/
def completeBatchIfTxOnChain (w : Wallet) (b : DbBatchTransfer) :
    Net (Option (Wallet × TransferStatus)) := do
  let some t := b.txid | return none
  if (confirmationsOf (← get).chain t).isNone then return none
  return some (← w.broadcastOp b.idx, .waitingConfirmations)

/-- `settle_untrusted_batch`: with a sender proxy that cannot be trusted, the operation completes
if its transaction is on chain, fails once its broadcast deadline has passed, and otherwise
waits, reporting `waiting`. -/
def settleUntrustedBatch (w : Wallet) (b : DbBatchTransfer) (waiting : Error) :
    Net (Wallet × Option TransferStatus) := do
  if let some (w', st) ← w.completeBatchIfTxOnChain b then return (w', some st)
  let now ← Net.now
  if !b.broadcastDeadlinePassed now then throw waiting
  return (w.failBatch now b.idx, some .failed)

/-- Complete an outgoing batch once every recipient ACKed (`try_complete_batch`):
a NACK fails it; an expired unreleased batch fails. A batch whose transaction was released to the
recipients is broadcast while no invoice has expired; past that it completes only if its
transaction is on chain, and fails once one of its inputs is spent elsewhere. -/
def tryCompleteBatch (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Option TransferStatus) := do
  let now ← Net.now
  let trs := (w.db.transfersOfBatch b.idx).filter (·.recipientId.isSome)
  if trs.any (·.ack == some false) then return (w.failBatch now b.idx, some .failed)
  if !trs.all (·.ack == some true) then return (w, none)
  let released := trs.all (·.ackSignature.isSome)
  if !released && b.isExpired now then return (w.failBatch now b.idx, some .failed)
  if released && trs.any (·.invoiceExpiration.any (· ≤ now + proxyClockSkewMarginSecs)) then
    if let some (w', st) ← w.completeBatchIfTxOnChain b then return (w', some st)
    if w.txInputsSpentElsewhere b (← get).chain then return (w.failBatch now b.idx, some .failed)
    return (w, none)
  return (← w.broadcastOp b.idx, some .waitingConfirmations)

/-- `wait_ack`: read the answers of the proxy recipients on the sender proxy (`ack.get`), keep
each ACK or NACK whose signature the recipient's key verifies, then try to complete the batch. A
proxy that lost the operation or serves an invalid signature cannot be trusted. -/
def waitAck (w : Wallet) (b : DbBatchTransfer) : Net (Wallet × Option TransferStatus) := do
  let trs := w.db.transfersOfBatch b.idx
  let mut ids : List String := []
  let mut senderProxy : Option String := none
  for t in trs do
    let some url := w.db.senderProxyOf? t.idx | continue
    let some tid := t.proxyTransferId
      | throw (.internal s!"transfer {t.idx} has a sender proxy endpoint but no transfer ID")
    ids := ids ++ [tid]
    if senderProxy.isNone then senderProxy := some url
  let some url := senderProxy | return (w, none)
  let sender : SecretKey := ⟨b.operationSecretKey.getD ""⟩
  match ← ProxyClient.getAck url ids sender with
  | .error e =>
    Net.ofResult (Proxy.checkGetAckError e)
    w.settleUntrustedBatch b .operationNotFound
  | .ok answers =>
    let mut w := w
    for t in trs do
      if t.ack.isSome || (w.db.endpointsOf t.idx).isEmpty then continue
      let some tid := t.proxyTransferId
        | throw (.internal s!"transfer {t.idx} has transport endpoints but no transfer ID")
      let (some ack, some sig) := (answers.acks.lookup tid, answers.signatures.lookup tid)
        | continue
      let some pk := t.recipientPubkey | throw (.internal "missing recipient pubkey")
      let some ch := t.consignmentHash | throw (.internal "missing consignment hash")
      if !verifyMessage pk (Proxy.Msg.ack tid ack ch) sig then
        return ← w.settleUntrustedBatch b .invalidContentSignature
      w := { w with db := w.db.updateTransfer t.idx fun x =>
        { x with ack := some ack, ackSignature := some (ProxyClient.sigHex sig) } }
    w.tryCompleteBatch b

/-- ACK a recipient out of band (`provide_out_of_band_ack`). -/
def provideOutOfBandAck (w : Wallet) (world : World) (o : Online) (recipientId : String) :
    Result (Wallet × World × Option Txid) := do
  w.checkOnline o
  let now := world.now
  let some tr := w.db.transfers.find? (·.recipientId == some recipientId)
    | throw (.cannotProvideOutOfBandAck "no transfer found for the provided recipient ID")
  let some b := w.db.batchOfAssetTransfer? tr.assetTransferIdx | throw (.internal "missing batch")
  if b.incoming then throw (.cannotProvideOutOfBandAck "only outgoing transfers can be ACKed")
  if b.status != .waitingCounterparty then
    throw (.cannotProvideOutOfBandAck "only WaitingCounterparty transfers can be ACKed")
  if w.db.endpoints.any fun e => e.transferIdx == tr.idx && e.kind == .recipientProxy then
    throw (.cannotProvideOutOfBandAck "recipient uses an automated transport; use refresh() to complete it instead")
  let w := { w with db := w.db.updateTransfer tr.idx fun t => { t with ack := some true } }
  let (r, world) := (w.tryCompleteBatch b).exec world
  let (w, st) ← r
  let w := w.updateBackupInfo now
  match st with
  | none => return (w, world, none)
  | some .waitingConfirmations => return (w, world, b.txid)
  | some _ => throw (.cannotProvideOutOfBandAck "transfer could not be completed")

/-! ## Refresh -/

/-- `refresh_transfer`: one waiting transfer, unless the filter leaves it out. A legacy transfer
waiting for its counterparty fails. A proxy recipient waiting for the broadcast asks the sender
proxy for the transaction when the chain does not show it yet. -/
def refreshTransfer (w : Wallet) (b : DbBatchTransfer) (filter : List RefreshFilter) :
    Net (Wallet × Option TransferStatus) := do
  if !filter.isEmpty then
    let requested := (RefreshTransferStatus.ofStatus? b.status).map (⟨·, b.incoming⟩)
    if !(requested.any filter.contains) then return (w, none)
  match b.status with
  | .waitingCounterparty =>
    if b.isLegacy then return (w.failBatch (← Net.now) b.idx, some .failed)
    if b.incoming then w.waitConsignment b else w.waitAck b
  | .waitingSafeHeight => w.waitSafeHeight b
  | .waitingBroadcast =>
    let some (_, tr) := w.db.incomingTransfer? b.idx | throw (.internal "missing transfer")
    if w.db.usesOutOfBand tr then w.waitConfirmations b
    else
      let (w, st) ← w.waitConfirmations b
      if st.isSome then return (w, st)
      w.waitBroadcast b
  | .waitingConfirmations => w.waitConfirmations b
  | _ => return (w, none)

/-- `add_invoice_transfer`: a later transfer to a reusable invoice gets an incoming transfer of
its own, a copy of the first one with the transfer id, using the proxy it was found on. -/
def addInvoiceTransfer (w : Wallet) (first : DbTransfer) (firstBatch : DbBatchTransfer)
    (inv : DbInvoice) (url tid : String) (now : Nat) : Wallet × DbTransfer := Id.run do
  let (bi, db) := w.db.fresh
  let (ati, db) := db.fresh
  let (ti, db) := db.fresh
  let batch : DbBatchTransfer :=
    { idx := bi, status := .waitingCounterparty, createdAt := now, updatedAt := now
      expiration := firstBatch.expiration, minConfirmations := firstBatch.minConfirmations
      incoming := true, operationSecretKey := firstBatch.operationSecretKey
      retentionDeadline := firstBatch.retentionDeadline }
  let recipientType := match first.recipientType with
    | some (.witness _) => some (RecipientTypeFull.witness none)
    | t => t
  let rid := first.recipientId.getD ""
  let tr : DbTransfer :=
    { idx := ti, assetTransferIdx := ati, requestedAssignment := first.requestedAssignment
      recipientId := first.recipientId, recipientType, invoiceString := first.invoiceString
      recipientPubkey := first.recipientPubkey, recipientEncryption := first.recipientEncryption
      invoiceIdx := first.invoiceIdx, proxyTransferId := some tid
      receiveDir := some s!"{rid.replace ":" "_"}_{(tid.take 16).toString}" }
  let eps := (w.db.recipientProxiesOf first.idx).map fun e =>
    ({ e with transferIdx := ti, used := e.endpoint == url } : DbTransferEndpoint)
  let db := { db with
    batchTransfers := db.batchTransfers ++ [batch]
    assetTransfers := db.assetTransfers ++ [⟨ati, true, bi, inv.assetId, none⟩]
    transfers := db.transfers ++ [tr]
    endpoints := db.endpoints ++ eps }
  return ({ w with db }, tr)

/-- `check_discovered_transfer`: a transfer found for a reusable invoice is kept only if its
consignment decrypts, matches its hash, is of a supported schema and of the invoice's asset, and
pays the invoice at a single destination with the derived blinding (it is not validated). -/
def checkDiscovered (w : Wallet) (first : DbTransfer) (inv : DbInvoice) (url tid : String)
    (res : Proxy.ConsignmentGetResult) (recipient : SecretKey) :
    Option (ProxyReceiveData × Payload) := do
  let te ← (TransportEndpoint.new res.senderTransportEndpoint).toOption
  let d : ProxyReceiveData :=
    { proxyUrl := url, transferId := tid, senderProxy := te.endpoint, senderPubkey := res.senderPk
      consignmentHash := res.consignmentHash, recipientEncryption := first.recipientEncryption
      batch := res.batch }
  guard (isPubkeyHex res.senderPk)
  let file ← (res.consignment.decryptWith first.recipientEncryption
    (deriveShared recipient res.senderPk).symKey res.consignmentHash).toOption
  let c ← file.consignment?
  let schema ← AssetSchema.ofSchemaId? c.schemaId
  guard (w.data.supportedSchemas.contains schema)
  guard (inv.assetId.all (· == toString c.contractId))
  let blinding ← ProxyClient.sealBlinding recipient res.senderPk
  let (_, beneficiary) ← (Beneficiary.parse (first.recipientId.getD "")).toOption
  guard ((findPayments c beneficiary (some blinding)).length == 1)
  return (d, file)

/-- `discover_invoice_transfers`: each live reusable invoice (of the asset, if given) asks its
recipient proxies for its transfers. A pending one not known yet, posted by its sender and
passing the checks, is saved: the first goes to the receive made with the invoice, each later
one gets an incoming transfer of its own, until the quota is reached. One that fails the checks
is NACKed and deleted, as is a transfer that failed locally. -/
def discoverInvoiceTransfers (w : Wallet) (assetId : Option String) : Net Wallet := do
  let now ← Net.now
  let invoices := w.db.invoices.filter fun i =>
    i.live now && (assetId.isNone || i.assetId == assetId)
  let mut w := w
  for inv in invoices do
    let its := ((w.db.transfers.filter (·.invoiceIdx == some inv.idx)).mergeSort
      fun a c => a.idx ≤ c.idx).filterMap fun t =>
        (w.db.batchOfAssetTransfer? t.assetTransferIdx).map (t, ·)
    let some (first, firstBatch) := its.head? | continue
    let mut known := its.filterMap (·.1.proxyTransferId)
    let failed := (its.filter (·.2.status == .failed)).filterMap (·.1.proxyTransferId)
    let mut active :=
      (its.filter fun (t, b) => t.proxyTransferId.isSome && b.status != .failed).length
    let mut firstFree := first.proxyTransferId.isNone && firstBatch.status == .waitingCounterparty
    if active ≥ inv.quota && failed.isEmpty then continue
    let iid := invoiceId (first.recipientId.getD "") (first.recipientPubkey.getD "")
    let recipient : SecretKey := ⟨firstBatch.operationSecretKey.getD ""⟩
    for e in w.db.recipientProxiesOf first.idx do
      let some listed ← ProxyClient.listInvoiceTransfers e.endpoint iid recipient | continue
      for (tid, st) in listed do
        if failed.contains tid then
          ProxyClient.releaseTransferData e.endpoint tid recipient true
          continue
        if st != .pending || active ≥ inv.quota || known.contains tid then continue
        let .ok res ← ProxyClient.getConsignment e.endpoint tid | continue
        if !Proxy.postedBySender iid tid res then
          ProxyClient.releaseTransferData e.endpoint tid recipient true
          continue
        match w.checkDiscovered first inv e.endpoint tid res recipient with
        | some (d, file) =>
          let (w', tr) := if firstFree then
              ({ w with db := w.db.setEndpointUsed first.idx e.endpoint true }, first)
            else w.addInvoiceTransfer first firstBatch inv e.endpoint tid now
          w ← w'.recordReceived tr d file
          firstFree := false
          known := known ++ [tid]
          active := active + 1
        | none =>
          if let .ok te := TransportEndpoint.new res.senderTransportEndpoint then
            discard (Net.attempt
              (ProxyClient.signAndPostAck te.endpoint tid false res.consignmentHash recipient))
          ProxyClient.releaseTransferData e.endpoint tid recipient true
  return w

/-- Refresh every waiting transfer (`refresh`), of an asset if given, those the filter keeps:
transfers to reusable invoices are discovered first; then each transfer independently. A failure
is reported for its batch and leaves it unchanged, while what it did on the proxies, the chain and
the wallet's files stays. -/
def refresh (w : Wallet) (world : World) (o : Online) (assetId : Option String := none)
    (filter : List RefreshFilter := []) :
    Result (Wallet × World × List (Nat × RefreshedTransfer)) := do
  w.checkOnline o
  let now := world.now
  if let some id := assetId then discard (w.asset? id)
  let discover := filter.isEmpty || filter.contains ⟨.waitingCounterparty, true⟩
  let (r, world) := (if discover then w.discoverInvoiceTransfers assetId else pure w).exec world
  let mut w ← r
  let mut world := world
  let mut out : List (Nat × RefreshedTransfer) := []
  let batches := w.db.batchTransfers.filter fun b =>
    b.status.isWaiting &&
      assetId.all fun id => (w.db.assetTransfersOf b.idx).any (·.assetId == some id)
  for b in batches do
    let (r, world') := (w.refreshTransfer b filter).exec world
    world := world'
    match r with
    | .ok (w', st) =>
      w := w'
      out := out ++ [(b.idx, ⟨st, none⟩)]
    | .error e => out := out ++ [(b.idx, ⟨none, some (reprStr e)⟩)]
  let changed := out.any (·.2.updatedStatus.isSome)
  return (if changed then w.updateBackupInfo now else w, world, out)

/-! ## Failing and deleting -/

/-- What `try_fail_batch_transfer` did. -/
inductive TryFailOutcome where
  | failed
  | refreshed
  | denied
  deriving DecidableEq, Repr, Inhabited

/-- `clean_sender_ack`: revoke the signed transactions of an outgoing operation on its sender
proxy (`ack.clean`); one with nothing registered there counts as revoked. -/
def cleanSenderAck (w : Wallet) (b : DbBatchTransfer) : Net Proxy.CleanAckOutcome := do
  let some seed := b.operationSecretKey | return .revoked
  let trs := (w.db.transfersOfBatch b.idx).filter fun t => (w.db.senderProxyOf? t.idx).isSome
  let some url := trs.head?.bind fun t => w.db.senderProxyOf? t.idx | return .revoked
  let ids := (trs.filterMap (·.proxyTransferId)).mergeSort fun a c => compare a c != .gt
  Net.ofResult (Proxy.cleanAckOutcome (← ProxyClient.cleanAck url ids ⟨seed⟩))

/-- `blind_receive_may_be_failed`: a blind receive reserved on proxies keeps its UTXO until its
expiration has passed on the proxies' clocks too and then, on each recipient proxy, either no
transfer is pending (or the proxy no longer knows the invoice) or the retention deadline has
passed. -/
def blindReceiveMayBeFailed (w : Wallet) (b : DbBatchTransfer) : Net Bool := do
  let now ← Net.now
  let some deadline := b.retentionDeadline | return true
  if !b.isExpired now then return true
  if !b.isExpiredWithMargin now proxyClockSkewMarginSecs then return false
  if deadline + proxyClockSkewMarginSecs < now then return true
  let some (_, tr) := w.db.incomingTransfer? b.idx | throw (.internal "missing transfer")
  let (some rid, some pk, some seed) := (tr.recipientId, tr.recipientPubkey, b.operationSecretKey)
    | return true
  let iid := invoiceId rid pk
  for e in w.db.recipientProxiesOf tr.idx do
    let nothingPending := match ← Net.attempt (ProxyClient.listTransfers e.endpoint iid ⟨seed⟩) with
      | .ok (.ok l) => l.all (·.2 != .pending)
      | .ok (.error err) => err == .invoiceNotReserved
      | .error _ => false
    if !nothingPending then return false
  return true

/-- `try_fail_batch_transfer`: refresh the transfer first (it may progress, or fail by itself);
then a received mint the refresh checked cannot fail, an outgoing transfer whose transaction is
on chain completes, one every recipient ACKed cannot fail, and a deliberate fail revokes the
signed transaction on the sender proxy (a released one denies the fail); a blind receive keeps
its UTXO while a transfer to it can be downloaded. -/
def tryFailBatchTransfer (w : Wallet) (b : DbBatchTransfer) (revokeReleased : Bool) :
    Net (Wallet × TryFailOutcome) := do
  let now ← Net.now
  let expired := if b.incoming then b.incomingExpired now else b.expiredBeyondSkewMargin now
  let mut w := w
  let mut st : Option TransferStatus := none
  match ← Net.attempt (w.refreshTransfer b []) with
  | .ok (w', s) =>
    w := w'
    st := s
  | .error (.minFeeNotMet _) | .error (.maxFeeExceeded _) => pure ()
  | .error e =>
    if !b.incoming && (e == .operationNotFound || e == .invalidContentSignature) then
      return (w, .denied)
    if !expired then throw e
  if let some s := st then return (w, if s == .failed then .failed else .refreshed)
  -- a received mint expires only by its lock, which may have been made already
  if b.incoming && w.isMint b then return (w, .denied)
  if !b.incoming && b.status == .waitingCounterparty then
    if let some (w', _) ← w.completeBatchIfTxOnChain b then return (w', .refreshed)
    let trs := w.db.transfersOfBatch b.idx
    if !trs.isEmpty && trs.all (·.ack == some true) then return (w, .denied)
  if revokeReleased && !b.incoming then
    match ← w.cleanSenderAck b with
    | .revoked => pure ()
    | .released => return (w, .denied)
    | .unknown =>
      if b.status == .waitingCounterparty && !b.broadcastDeadlinePassed now then
        return (w, .denied)
  if b.incoming && b.status == .waitingCounterparty && !(← w.blindReceiveMayBeFailed b) then
    return (w, .denied)
  return (w.failBatch now b.idx, .failed)

/-- `fail_transfers_impl`: the wallet after it, whether a transfer changed, and whether the
requested transfer could not be failed. A mint expires by its lock, not by a timestamp: a sent
one not ended fails once its lock expired (with an index, unless only transfers without an asset
may fail; without, after the expired transfers, a lock that cannot be checked being skipped), a
checked received one never. -/
def failTransfersStep (w : Wallet) (batchIdx : Option Nat) (noAssetOnly : Bool) :
    Net (Wallet × Bool × Bool) := do
  let now ← Net.now
  let hasAsset (bi : Nat) : Bool := (w.db.assetTransfersOf bi).any (·.assetId.isSome)
  match batchIdx with
  | some bi =>
    let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
    if !b.status.isFallible then return (w, false, true)
    if w.isMint b then
      if b.incoming || noAssetOnly then return (w, false, true)
      let (w, failed) ← w.failExpiredMint b
      return (w, failed, !failed)
    if b.status == .waitingBroadcast && !b.incomingExpired now then return (w, false, true)
    if noAssetOnly && hasAsset bi then return (w, false, true)
    let (w, outcome) ← w.tryFailBatchTransfer b true
    return (w, true, outcome != .failed)
  | none =>
    let fallible := w.db.batchTransfers.filter (·.status.isFallible)
    let sentMints := fallible.filter fun b => !b.incoming && w.isMint b
    let expired := fallible.filter fun b => !w.isMint b &&
      (if b.incoming then b.incomingExpired now else b.expiredBeyondSkewMargin now)
    let mut w := w
    let mut changed := false
    for b in expired do
      if noAssetOnly && hasAsset b.idx then continue
      let (w', outcome) ← w.tryFailBatchTransfer b false
      w := w'
      if outcome != .denied then changed := true
    if !noAssetOnly then
      for b in sentMints do
        match ← Net.attempt (w.failExpiredMint b) with
        | .ok (w', failed) =>
          w := w'
          if failed then changed := true
        | .error _ => pure ()
    return (w, changed, false)

/-- Fail transfers (`fail_transfers`): with an index, a fallible transfer that no counterparty
can still complete; without, every expired fallible one and every sent mint whose lock expired.
What it did is kept even when it then reports that the requested transfer cannot be failed. -/
def failTransfers (w : Wallet) (world : World) (o : Online) (batchIdx : Option Nat := none)
    (noAssetOnly : Bool := false) : Wallet × World × Result Bool :=
  match w.checkOnline o with
  | .error e => (w, world, .error e)
  | .ok () =>
    match (w.failTransfersStep batchIdx noAssetOnly).exec world with
    | (.ok (w', changed, cannotFail), world') =>
      let w' := if changed then w'.updateBackupInfo world.now else w'
      (w', world', if cannotFail then .error .cannotFailBatchTransfer else .ok changed)
    | (.error e, world') => (w, world', .error e)

/-- Delete failed transfers (`delete_transfers`); their colorings, their transport endpoints and
the outputs they registered but never saw go too: those they color and those of their transaction
no other transfer colors, as the rows were before the deletion. -/
def deleteTransfers (w : Wallet) (now : Nat) (batchIdx : Option Nat := none) (noAssetOnly : Bool := false) :
    Result (Wallet × Bool) := do
  let liveInvoice (bi : Nat) : Bool :=
    (w.db.assetTransfersOf bi).any fun a => (w.db.transfersOf a.idx).any fun t =>
      t.invoiceIdx.any fun ii => w.db.invoices.any fun inv => inv.idx == ii && inv.live now
  let hasAsset (bi : Nat) : Bool := (w.db.assetTransfersOf bi).any (·.assetId.isSome)
  let targets ← match batchIdx with
    | some bi =>
      let some b := w.db.batch? bi | throw (.batchTransferNotFound bi)
      if b.status != .failed || liveInvoice bi || (noAssetOnly && hasAsset bi) then
        throw .cannotDeleteBatchTransfer
      pure [bi]
    | none => pure ((w.db.batchTransfers.filter fun b =>
        b.status == .failed && !liveInvoice b.idx && !(noAssetOnly && hasAsset b.idx)).map (·.idx))
  let before := w.db
  let unseen (bi : Nat) : List Nat :=
    let ats := (before.assetTransfersOf bi).map (·.idx)
    let txid := (before.batch? bi).bind (·.txid)
    let colored (t : DbTxo) (mine : Bool) : Bool := before.colorings.any fun c =>
      c.txoIdx == t.idx && ats.contains c.assetTransferIdx == mine
    (before.txos.filter fun t => !t.exists_ &&
      (colored t true || (txid == some t.outpoint.txid && !colored t false))).map (·.idx)
  let db := targets.foldl (fun db bi =>
    let ats := (db.assetTransfersOf bi).map (·.idx)
    let gone := (db.transfers.filter fun t => ats.contains t.assetTransferIdx).map (·.idx)
    let txos := unseen bi
    { db with
      colorings := db.colorings.filter fun c => !ats.contains c.assetTransferIdx
      txos := db.txos.filter fun t => !txos.contains t.idx
      transfers := db.transfers.filter fun t => !ats.contains t.assetTransferIdx
      endpoints := db.endpoints.filter fun e => !gone.contains e.transferIdx
      assetTransfers := db.assetTransfers.filter fun a => a.batchTransferIdx != bi
      batchTransfers := db.batchTransfers.filter (·.idx != bi)
      reserved := db.reserved.filter (·.forColored != some bi) }) w.db
  let w := { w with db }
  return (if targets.isEmpty then w else w.updateBackupInfo now, !targets.isEmpty)

end Wallet

end Rgb.Lib
