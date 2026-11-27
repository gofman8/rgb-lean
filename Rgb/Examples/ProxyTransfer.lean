import Rgb.Lib.Refresh
import Rgb.Lib.StateMachine
import Rgb.Lib.Contracts
import Rgb.Lib.Operations
import Rgb.Examples.Transfer
import Rgb.Examples.SafeHeight

/-!
# Transfers through an RGB proxy

The wallets of the transfer scenarios exchange consignments, ACKs and the signed transaction
through a proxy. Bob reserves a blind invoice on it; Alice sends to it: her consignment waits on
the proxy and her operation is registered there with the signed transaction encrypted for Bob.
Bob's refresh downloads, validates and ACKs; his ACK completes the operation, so the proxy
releases the transaction to him and he broadcasts it. Alice's refresh reads his signed ACK and
completes her send. Both settle once a block confirms the transaction. Then a batch released on
its last ACK, a witness receive and the destinations of a payment, address reuse, NACKs, the
sender proxy retention grace, the checks of a send, unreachable, draining and authenticated
proxies, a reusable invoice, expiration, revocation, forged downloads, spam and copies sent to a
reusable invoice, a sender proxy that cannot be trusted, a released send near its invoice
expiration, ending a send and its refused posts, a download kept after a failed refresh, answers
already on the sender proxy, a receiver without encryption, unsafe history through the proxy,
legacy transfers and an expired reusable invoice.
-/

namespace Rgb.Examples.ProxyTransferScenario

open Rgb Rgb.Lib Rgb.Lib.ProxyCrypto Rgb.Examples.WalletScenario Rgb.Examples.TransferScenario

def url : String := "http://proxy.test/json-rpc"
def endpoint : String := "rpc://proxy.test/json-rpc"
/-- The world of the transfer scenarios with a proxy answering at `url`. -/
def wp : World := world2.withProxy (Proxy.Server.init url world2.now)

/-- The proxy at `u` in a world. -/
def proxyOf (w : World) (u : String := url) : Proxy.Server := (w.proxies.lookup u).getD default

/-- A world where the proxy at its URL is `s`. -/
def withServer (w : World) (s : Proxy.Server) : World :=
  { w with proxies := w.proxies.map fun (u, x) => (u, if u == s.url then s else x) }

/-- `n` copies of `c`. -/
def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

/-- The world one block later, `secs` later. -/
def mined (w : World) (secs : Nat := 600) : World :=
  { w with chain := w.chain.mine }.setTime (w.now + secs)

/-- What a refresh gives: the wallet, the world and the outcome per batch. -/
abbrev Refreshed := Wallet × World × List (Nat × RefreshedTransfer)

/-- A refresh that must succeed. -/
def refreshed (w : Wallet) (world : World) (o : Online) : Refreshed :=
  (w.refresh world o).toOption.get!

/-- The outcome a refresh reports for a batch. -/
def reported (r : Refreshed) (i : Nat) : Option RefreshedTransfer := r.2.2.lookup i

/-- The outcomes a refresh reports, in batch order. -/
def outcomes (r : Refreshed) : List RefreshedTransfer := r.2.2.map (·.2)

/-- The outgoing batch of a transaction. -/
def batchOf (w : Wallet) (t : Txid) : Nat := ((w.db.batchByTxid? t false).map (·.idx)).getD 0

/-- A receive of Bob through the proxy that must succeed. -/
def bobReceive (w : Wallet) (world : World) (n : UInt64) (quota : Nat := 1) (witness := false) :
    Wallet × World × ReceiveData :=
  (w.receive world witness none (.fungible n) (world2.now + 86400) [endpoint] (quota := quota)
    (online := some bobO)).toOption.get!

/-- A send of Alice's USDT, with `endpoint` as her sender proxy. -/
def aliceBegin (w : Wallet) (world : World) (rs : List Recipient) (exp : Nat := world2.now + 3600)
    (senderEndpoint : Option String := some endpoint) : Result (Wallet × PendingOp) :=
  w.sendBegin world aliceO [(usdt, rs)] false 1 1 exp senderEndpoint

/-- The end of a send that must succeed. -/
def aliceEnd (b : Wallet × PendingOp) (world : World) :
    Wallet × World × List (String × Consignment) :=
  (b.1.sendEnd world aliceO b.2.txid).toOption.get!

/-- Invoice expiration and operation expiration of the sends. -/
def exp : Nat := world2.now + 86400
def opExp : Nat := world2.now + 3600

/-- A proxy recipient paying `n` to a receive. -/
def toProxy (d : ReceiveData) (n : UInt64) : Recipient :=
  { recipientId := d.recipientId, assignment := .fungible n, transportEndpoints := [endpoint]
    publicKey := some d.publicKey, expirationTimestamp := some exp }

/-! ## A blind receive reserved on a proxy -/

def r1 : Wallet × World × ReceiveData := bobReceive bob1 wp 600
def bobR : Wallet := r1.1
def wR : World := r1.2.1
def inv1 : ReceiveData := r1.2.2
def iid1 : String := invoiceId inv1.recipientId inv1.publicKey

-- the proxy did not know the invoice before the receive
#guard (proxyOf wp).invoiceCheck [iid1] == [(iid1, .unknown)]
-- the receive reserved it
#guard (proxyOf wR).invoiceCheck [iid1] == [(iid1, .available)]
-- the receive keeps its retention deadline: the expiration plus the proxy's grace of a day
#guard (bobR.db.batch? inv1.batchTransferIdx).bind (·.retentionDeadline) == some (exp + 86400)
-- its endpoint is stored as the proxy's HTTP URL, not used yet
#guard bobR.db.endpoints.map (fun e => (e.endpoint, e.kind, e.used))
  == [(url, .recipientProxy, false)]
-- its operation key is in its batch; the invoice carries the public key
#guard ((bobR.db.batch? inv1.batchTransferIdx).bind (·.operationSecretKey)).map
  (fun s => (⟨s⟩ : SecretKey).pk) == some inv1.publicKey

/-! ## Sending through it -/

def toBobP : Recipient := toProxy inv1 600
def begunP : Wallet × PendingOp := (aliceBegin alice5 wR [toBobP]).toOption.get!
def endedP : Wallet × World × List (String × Consignment) := aliceEnd begunP wR
def aliceP : Wallet := endedP.1
def wS : World := endedP.2.1
def sendIdx : Nat := batchOf aliceP begunP.2.txid
def senderPk : String := (⟨begunP.2.operationSecretKey.getD ""⟩ : SecretKey).pk
def tidP : String := transferId iid1 senderPk

-- the consignment waits on the proxy
#guard (proxyOf wS).transferList iid1 == .ok [(tidP, .pending)]
-- it took the invoice's quota
#guard (proxyOf wS).invoiceCheck [iid1] == [(iid1, .full)]
-- the operation is registered on the sender proxy
#guard (proxyOf wS).operations.contains senderPk
-- the send waits for the ACK until its broadcast deadline: the expiration plus the sender grace
#guard (aliceP.db.batch? sendIdx).map (fun b => (b.status, b.broadcastDeadline))
  == some (.waitingCounterparty, some (opExp + 86400))
def sentRow : DbTransfer := (aliceP.db.transfersOfBatch sendIdx).headD default
-- the recipient's row keeps the proxy transfer id, the consignment hash and the recipient's key
#guard sentRow.proxyTransferId == some tidP && sentRow.consignmentHash.isSome &&
  sentRow.recipientPubkey == some inv1.publicKey
-- the endpoint the consignment was posted to is used; the sender proxy is kept for the ACK
#guard (aliceP.db.endpointsOf sentRow.idx).map (fun e => (e.endpoint, e.kind, e.used))
  == [(url, .recipientProxy, true), (url, .senderProxy, false)]

/-! ## The receiver downloads, validates and ACKs -/

def bobRef : Refreshed := refreshed bobR wS bobO

-- Bob's ACK completes the operation: the proxy releases the transaction, Bob broadcasts it
#guard reported bobRef inv1.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩
-- the transaction is in the mempool
#guard (bobRef.2.1.chain.findMempool? begunP.2.txid).isSome
-- the broadcast deadline: the operation expiration plus the sender proxy's grace
#guard (bobRef.1.db.batch? inv1.batchTransferIdx).bind (·.broadcastDeadline)
  == some (opExp + 86400)
-- the released transaction is kept, to be broadcast again if it goes missing
#guard (bobRef.2.1.filesOf bobR.fingerprint).releasedTxs.map (·.2.txid) == [begunP.2.txid]
-- the proxy may drop the consignment; the transfer keeps its quota slot
#guard (proxyOf bobRef.2.1).transferList iid1 == .ok [(tidP, .retrieved)]
-- the payment is pending in Bob's balance
#guard bobRef.1.assetBalance usdt == ⟨0, 600, 0⟩
-- a released transaction missing from the mempool is broadcast again until the deadline
def evicted : World := { bobRef.2.1 with chain := bobRef.2.1.chain.evict begunP.2.txid }
#guard ((refreshed bobRef.1 evicted bobO).2.1.chain.findMempool? begunP.2.txid).isSome
-- past the deadline it is not broadcast again
#guard ((refreshed bobRef.1 (evicted.setTime (opExp + 86400 + 10)) bobO).2.1.chain.findMempool?
  begunP.2.txid).isNone
-- a day past the deadline, still unconfirmed, the receive fails
#guard reported (refreshed bobRef.1 (bobRef.2.1.setTime (opExp + 2 * 86400 + 1)) bobO)
  inv1.batchTransferIdx == some ⟨some .failed, none⟩
#guard validPath true [.waitingCounterparty, .waitingConfirmations, .failed]

/-! ## The sender reads the ACK and completes -/

def aliceRef : Refreshed := refreshed aliceP bobRef.2.1 aliceO

-- Alice checks Bob's signature on his ACK and broadcasts (Bob already did)
#guard reported aliceRef sendIdx == some ⟨some .waitingConfirmations, none⟩
-- she keeps the ACK with its signature
#guard ((aliceRef.1.db.transfersOfBatch sendIdx).map fun t => (t.ack, t.ackSignature.isSome))
  == [(some true, true)]

/-! ## Both settle once a block confirms the transaction -/

def bobDoneP : Refreshed := refreshed bobRef.1 (mined aliceRef.2.1) bobO
def aliceDoneP : Refreshed := refreshed aliceRef.1 bobDoneP.2.1 aliceO

-- Bob holds the 600 he received
#guard bobDoneP.1.assetBalance usdt == ⟨600, 600, 600⟩
-- Alice holds her change of 400
#guard aliceDoneP.1.assetBalance usdt == ⟨400, 400, 400⟩
-- both transfers are settled
#guard statusOf bobDoneP.1 inv1.batchTransferIdx == some .settled &&
  statusOf aliceDoneP.1 sendIdx == some .settled
-- the receiver's path is one of the status machine
#guard validPath true [.waitingCounterparty, .waitingConfirmations, .settled]
-- the sender's path is one of the status machine
#guard validPath false [.initiated, .waitingCounterparty, .waitingConfirmations, .settled]

/-! ## A donation through the proxy -/

def begunD : Wallet × PendingOp :=
  (alice5.sendBegin wR aliceO [(usdt, [toBobP])] true 1 1 opExp (some endpoint)).toOption.get!
def endedD : Wallet × World × List (String × Consignment) := aliceEnd begunD wR
-- a donation registers no operation on the sender proxy and is broadcast at once
#guard (proxyOf endedD.2.1).operations.isEmpty &&
  (endedD.2.1.chain.findMempool? begunD.2.txid).isSome
def bobD : Refreshed := refreshed bobR endedD.2.1 bobO
-- Bob's ACK finds no operation: as a donation it waits for confirmations, with no deadline
#guard reported bobD inv1.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩ &&
  ((bobD.1.db.batch? inv1.batchTransferIdx).bind (·.broadcastDeadline)).isNone

/-! ## A batch to two receives: the last ACK releases the transaction -/

def rb1 : Wallet × World × ReceiveData := bobReceive bob1 wp 100
def rb2 : Wallet × World × ReceiveData := bobReceive rb1.1 rb1.2.1 200
def begunB : Wallet × PendingOp :=
  (aliceBegin alice5 rb2.2.1 [toProxy rb1.2.2 100, toProxy rb2.2.2 200]).toOption.get!
def endedB : Wallet × World × List (String × Consignment) := aliceEnd begunB rb2.2.1
def bobB : Refreshed := refreshed rb2.1 endedB.2.1 bobO

-- the first ACK releases nothing yet; the second completes the operation
#guard outcomes bobB == [⟨some .waitingBroadcast, none⟩, ⟨some .waitingConfirmations, none⟩]
-- with the transaction gone from the mempool, the first receive gets it on its next ACK
def bobB2 : Refreshed :=
  refreshed bobB.1 { bobB.2.1 with chain := bobB.2.1.chain.evict begunB.2.txid } bobO
#guard reported bobB2 rb1.2.2.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩
-- and broadcasts it
#guard (bobB2.2.1.chain.findMempool? begunB.2.txid).isSome
-- the first receive's path is one of the status machine
#guard validPath true [.waitingCounterparty, .waitingBroadcast, .waitingConfirmations, .settled]
def batchIdx : Nat := batchOf endedB.1 begunB.2.txid
def aliceBatch : Refreshed := refreshed endedB.1 bobB.2.1 aliceO
-- Alice reads and keeps both signed ACKs, then completes the batch
#guard reported aliceBatch batchIdx == some ⟨some .waitingConfirmations, none⟩ &&
  ((aliceBatch.1.db.transfersOfBatch batchIdx).map fun t => (t.ack, t.ackSignature.isSome))
    == [(some true, true), (some true, true)]

/-! ## A witness receive through the proxy -/

def rw : Wallet × World × ReceiveData := bobReceive bob1 wp 50 (witness := true)
def toBobW : Recipient := { toProxy rw.2.2 50 with witnessData := some ⟨1000, none⟩ }
def begunW : Wallet × PendingOp := (aliceBegin alice5 rw.2.1 [toBobW]).toOption.get!
def endedW : Wallet × World × List (String × Consignment) := aliceEnd begunW rw.2.1
def bobWSeed : String :=
  ((rw.1.db.batch? rw.2.2.batchTransferIdx).bind (·.operationSecretKey)).getD ""
def aliceWPk : String := SecretKey.pk ⟨begunW.2.operationSecretKey.getD ""⟩

-- the witness seal is blinded with the blinding both keys derive
#guard (begunW.2.recipients.flatMap (·.2)).map (·.blinding)
  == [(deriveShared ⟨bobWSeed⟩ aliceWPk).sealBlinding]
-- the sender may not choose it
#guard (aliceBegin alice5 rw.2.1 [{ toBobW with witnessData := some ⟨1000, some 7⟩ }]).map
    (·.2.txid)
  == .error (.invalidRecipientData
    "cannot provide a blinding for a witness recipient with transport endpoints")
def bobW : Refreshed := refreshed rw.1 endedW.2.1 bobO
-- Bob finds the payment with that blinding, ACKs and broadcasts the released transaction
#guard reported bobW rw.2.2.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩
-- the output paying Bob waits for the transfer to settle
#guard (bobW.1.db.txos.filter (·.pendingWitness)).length == 1
def bobWDone : Wallet := (refreshed bobW.1 (mined bobW.2.1) bobO).1
-- once settled, Bob holds the 50 on it
#guard bobWDone.assetBalance usdt == ⟨50, 50, 50⟩ &&
  (bobWDone.db.txos.filter (·.pendingWitness)).isEmpty
-- a witness receive keeps no retention deadline
#guard (rw.1.db.batch? rw.2.2.batchTransferIdx).bind (·.retentionDeadline) == none

/-- The consignment paying Bob's witness receive. -/
def cW : Consignment := (endedW.2.2.headD default).2
/-- Bob's address. -/
def addrW : Script := rw.1.coloredScript (rw.1.coloredNext - 1)
/-- The blinding both keys derive. -/
def blW : UInt64 := (deriveShared ⟨bobWSeed⟩ aliceWPk).sealBlinding
/-- Destinations of a consignment for Bob's witness receive: vout and assignments received. -/
def destsW (c : Consignment) : List (Nat × Nat) :=
  (Wallet.findPayments c (.witnessVout addrW) (some blW)).map fun (_, v, r) => (v, r.length)
/-- `c` with an assignment at `vout` with blinding `bl` after each one with Bob's blinding. -/
def addAssign (c : Consignment) (vout : UInt32) (bl : UInt64) : Consignment :=
  let more (x : BuilderSeal GraphSeal × RevealedValue) := match x.1 with
    | .revealed g =>
      if g.blinding == blW then [x, (.revealed ⟨.witnessTx, vout, bl⟩, x.2)] else [x]
    | _ => [x]
  let fixTa (ta : TypedAssigns GraphSeal) : TypedAssigns GraphSeal := match ta with
    | .fungible items => .fungible (items.flatMap more)
    | other => other
  let fixKt (kt : KnownTransition) : KnownTransition := { kt with transition :=
    { kt.transition with assignments := kt.transition.assignments.mapValues fixTa } }
  let fixWb (wb : WitnessBundle) : WitnessBundle :=
    let kts := wb.bundle.knownTransitions.map fixKt
    { wb with bundle := { wb.bundle with knownTransitions := kts } }
  { c with bundles := c.bundles.map fixWb }
/-- `c` with its witness's output 1 paid again at an extra last output. -/
def addOutput (c : Consignment) : Consignment :=
  { c with bundles := c.bundles.map fun wb =>
      { wb with tx := { wb.tx with outputs := wb.tx.outputs ++ (wb.tx.outputAt? 1).toList } } }

-- one destination, vout 1, receiving one assignment
#guard destsW cW == [(1, 1)]
-- every assignment at that vout is received there, whatever its blinding
#guard destsW (addAssign cW 1 (blW + 1)) == [(1, 2)]
/-- The number of outputs of the witness paying Bob. -/
def outsW : Nat := (cW.bundles.headD default).tx.outputs.length
-- an address paid at two vouts by one bundle is paid at two destinations
#guard destsW (addAssign (addOutput cW) outsW.toUInt32 blW) == [(1, 1), (outsW, 1)]

-- an address to reuse must be revealed
#guard (bob1.witnessReceive wp none (.fungible 10) exp [endpoint] (online := some bobO)
    (address := some (bob1.coloredScript (bob1.coloredNext + 1)))).map (·.2.2.recipientId)
  == .error (.cannotReuseAddress "not revealed yet")
-- and of the colored keychain
#guard (bob1.witnessReceive wp none (.fungible 10) exp [endpoint] (online := some bobO)
    (address := some (bob1.vanillaScript 0))).map (·.2.2.recipientId)
  == .error (.cannotReuseAddress "not an address of the wallet's colored keychain")
def oobW : Wallet × World × ReceiveData :=
  (bob1.witnessReceive wp none (.fungible 10) exp [] (online := some bobO)).toOption.get!
-- an earlier out-of-band receive on it would not tell its payments apart
#guard (oobW.1.witnessReceive oobW.2.1 none (.fungible 10) exp [endpoint] (online := some bobO)
    (address := some (oobW.1.coloredScript (oobW.1.coloredNext - 1)))).map (·.2.2.recipientId)
  == .error (.cannotReuseAddress "an earlier witness receive on it used the out-of-band exchange")
def reusedW : Wallet × World × ReceiveData :=
  (rw.1.witnessReceive rw.2.1 none (.fungible 20) exp [endpoint] (online := some bobO)
    (address := some addrW)).toOption.get!
-- an earlier proxy receive on it shares it: its data goes under the recipient id
#guard reusedW.2.2.recipientId == rw.2.2.recipientId &&
  (reusedW.1.db.transfers.map (·.receiveDir)).head?
    == some (some (rw.2.2.recipientId.replace ":" "_"))

/-! ## A NACK of an invalid consignment fails the send -/

def bobKnows : Wallet :=
  (bob1.importContract world2.now (alice5.exportContract usdt).toOption.get!).toOption.get!
def rn : Wallet × World × ReceiveData :=
  (bobKnows.blindReceive wp (some usdt) (.fungible 10) exp [endpoint]
    (online := some bobO)).toOption.get!
def euro : Wallet × DbAsset :=
  (alice5.issueAssetNia world2.now "EUR" "Euro" 2 [500]).toOption.get!
def begunN : Wallet × PendingOp :=
  (euro.1.sendBegin rn.2.1 aliceO [(euro.2.id, [toProxy rn.2.2 10])] false 1 1 opExp
    (some endpoint)).toOption.get!
def endedN : Wallet × World × List (String × Consignment) := aliceEnd begunN rn.2.1
def bobN : Refreshed := refreshed rn.1 endedN.2.1 bobO
def aliceN : Refreshed := refreshed endedN.1 bobN.2.1 aliceO
def tidN : String :=
  transferId (invoiceId rn.2.2.recipientId rn.2.2.publicKey)
    (SecretKey.pk ⟨begunN.2.operationSecretKey.getD ""⟩)

-- Bob asked for USDT and gets EUR: he refuses it and his receive fails
#guard reported bobN rn.2.2.batchTransferIdx == some ⟨some .failed, none⟩
-- the proxy holds Bob's NACK
#guard ((proxyOf bobN.2.1).ackGet [tidN]).map (·.acks) == .ok [(tidN, false)]
-- Alice reads the signed NACK: her send fails
#guard reported aliceN (batchOf endedN.1 begunN.2.txid) == some ⟨some .failed, none⟩
-- the send's inputs are free again
#guard aliceN.1.db.reservedColored.isEmpty
-- both paths are of the status machine
#guard validPath true [.waitingCounterparty, .failed] &&
  validPath false [.initiated, .waitingCounterparty, .failed]

/-! ## A sender proxy that keeps a released transaction for less than a day -/

def shortUrl : String := "http://short.test/json-rpc"
def shortEndpoint : String := "rpc://short.test/json-rpc"
def wShort : World := wR.withProxy (Proxy.Server.init shortUrl world2.now 3600)
def begunG : Wallet × PendingOp :=
  (aliceBegin alice5 wShort [toBobP] (senderEndpoint := some shortEndpoint)).toOption.get!
def endedG : Wallet × World × List (String × Consignment) := aliceEnd begunG wShort
def bobG : Refreshed := refreshed bobR endedG.2.1 bobO
def aliceG : Refreshed := refreshed endedG.1 bobG.2.1 aliceO

-- the sender's broadcast deadline holds an hour of grace only
#guard (endedG.1.db.batch? (batchOf endedG.1 begunG.2.txid)).bind (·.broadcastDeadline)
  == some (opExp + 3600)
-- Bob NACKs on the sender proxy and fails
#guard reported bobG inv1.batchTransferIdx == some ⟨some .failed, none⟩
-- Alice reads the NACK and fails
#guard reported aliceG (batchOf endedG.1 begunG.2.txid) == some ⟨some .failed, none⟩

/-! ## The checks of a send -/

-- the invoice's quota is taken by Alice's first transfer
#guard (aliceBegin alice5 wS [{ toBobP with assignment := .fungible 100 }]).map (·.2.txid)
  == .error .invoiceQuotaExceeded
-- an invoice never reserved on the proxy
#guard (aliceBegin alice5 wp [{ toBobP with publicKey := some (rep 'a' 64) }]).map (·.2.txid)
  == .error .invoiceNotReserved
-- no endpoint of the recipient answers
#guard (aliceBegin alice5 wp [{ toBobP with transportEndpoints := ["rpc://nowhere.test"] }]).map
    (·.2.txid)
  == .error (.invalidTransportEndpoints "no valid transport endpoints")
-- a proxy recipient needs a sender endpoint
#guard (aliceBegin alice5 wR [toBobP] (senderEndpoint := none)).map (·.2.txid)
  == .error (.invalidTransportEndpoint "missing sender transport endpoint")
-- it needs the recipient's public key
#guard (aliceBegin alice5 wR [{ toBobP with publicKey := none }]).map (·.2.txid)
  == .error (.invalidPubkey "missing recipient public key")
-- a public key of 32 bytes
#guard (aliceBegin alice5 wR [{ toBobP with publicKey := some "abcd" }]).map (·.2.txid)
  == .error (.invalidPubkey "invalid Ed25519 public key length")
-- and the invoice expiration
#guard (aliceBegin alice5 wR [{ toBobP with expirationTimestamp := none }]).map (·.2.txid)
  == .error (.invalidRecipientData "missing invoice expiration")
-- the operation must expire well before the invoice
#guard (aliceBegin alice5 wR [toBobP] (exp - 599)).map (·.2.txid) == .error .invalidExpiration
-- unless it is a donation
#guard (alice5.sendBegin wR aliceO [(usdt, [toBobP])] true 1 1 (exp - 1) (some endpoint))
  matches .ok _
-- an invoice already expired
#guard (aliceBegin alice5 wR [{ toBobP with expirationTimestamp := some wR.now }]).map (·.2.txid)
  == .error .invoiceExpired
-- one expiring more than ten years ahead
#guard (aliceBegin alice5 wR
    [{ toBobP with expirationTimestamp := some (wR.now + maxExpirationSecs + 1) }]).map (·.2.txid)
  == .error .invalidExpiration
-- the sender endpoint is a JSON-RPC one
#guard (aliceBegin alice5 wR [toBobP] (senderEndpoint := some url)).map (·.2.txid)
  == .error .unsupportedTransportType

/-! ## Receiving through unreachable, draining and authenticated proxies -/

/-- A receive of 1 through `eps`. -/
def tryReceive (w : Wallet) (world : World) (eps : List String) (o : Option Online := some bobO) :
    Result (Wallet × World × ReceiveData) :=
  w.blindReceive world none (.fungible 1) exp eps (online := o)

-- no proxy answers: no endpoint is valid
#guard (tryReceive bob1 wp ["rpc://nowhere.test"]).map (·.2.2.recipientId)
  == .error .noValidTransportEndpoint
def wDrain : World := withServer wp ((proxyOf wp).configure fun c => { c with draining := true })
-- the only proxy is draining
#guard (tryReceive bob1 wDrain [endpoint]).map (·.2.2.recipientId) == .error .proxyDraining
-- a draining proxy is skipped when another one takes the invoice
#guard (tryReceive bob1 (wDrain.withProxy (Proxy.Server.init shortUrl world2.now))
  [endpoint, shortEndpoint]) matches .ok _
-- the endpoints of a receive are distinct
#guard (tryReceive bob1 wp [endpoint, endpoint]).map (·.2.2.recipientId)
  == .error (.invalidTransportEndpoints "no duplicate transport endpoints allowed")
-- and JSON-RPC ones
#guard (tryReceive bob1 wp [url]).map (·.2.2.recipientId) == .error .unsupportedTransportType
-- proxies need an online wallet
#guard (tryReceive bob1 wp [endpoint] none).map (·.2.2.recipientId) == .error .onlineNeeded

def authUrl : String := "http://auth.test/json-rpc"
def authEndpoint : String := "rpc://auth.test/json-rpc"
def authSeed : String := rep 'a' 64
def wAuth : World := world2.withProxy ((Proxy.Server.init authUrl world2.now).configure
  fun c => { c with authPk := some (SecretKey.pk ⟨authSeed⟩) })
-- an authentication key is a 32-byte seed
#guard (bob1.goOnline wAuth (proxyAuthKeys := [(authEndpoint, "zz")])).2.2
  == .error (.invalidProxyAuthKey
    "expected a hex-encoded 32-byte Ed25519 seed for endpoint rpc://auth.test/json-rpc")
-- one per proxy
#guard (bob1.goOnline wAuth
    (proxyAuthKeys := [(authEndpoint, authSeed), (authEndpoint, authSeed)])).2.2
  == .error (.duplicateProxyAuthKey ("endpoint rpc://auth.test/json-rpc resolves to a proxy URL " ++
    "(http://auth.test/json-rpc) already covered by another entry"))
def bobAuth : Wallet × Online × Result Unit :=
  bob1.goOnline wAuth (proxyAuthKeys := [(authEndpoint, authSeed)])
-- the proxy refuses a reservation without its key's signature
#guard (tryReceive bob1 wAuth [authEndpoint]).map (·.2.2.recipientId)
  == .error (.proxy "Missing: signature")
-- it takes one signed with the key the wallet went online with
#guard (tryReceive bobAuth.1 wAuth [authEndpoint] (some bobAuth.2.1)) matches .ok _
def wAR : World := wR.withProxy (proxyOf wAuth authUrl)
def aliceAuth : Wallet := (alice5.goOnline wAR (proxyAuthKeys := [(authEndpoint, authSeed)])).1
/-- A send to Bob's invoice with the authenticated proxy as sender proxy. -/
def begunA (w : Wallet) : Wallet × PendingOp :=
  (aliceBegin w wAR [toBobP] (senderEndpoint := some authEndpoint)).toOption.get!
-- without the key, the sender proxy refuses to register the operation
#guard ((begunA alice5).1.sendEnd wAR aliceO (begunA alice5).2.txid).map (·.2.2.length)
  == .error (.proxy "Missing: signature")
-- with it, the operation is registered there
#guard ((begunA aliceAuth).1.sendEnd wAR aliceO (begunA aliceAuth).2.txid) matches .ok _

/-! ## A reusable invoice taking two transfers -/

def rq : Wallet × World × ReceiveData := bobReceive bob1 wp 100 (quota := 2)
def iidQ : String := invoiceId rq.2.2.recipientId rq.2.2.publicKey
-- the invoice row is live until the retention deadline plus the clock skew margin
#guard rq.1.db.invoices.map (fun i => (i.quota, i.deadline)) == [(2, exp + 86400 + 300)]
-- its UTXO keeps a slot for each transfer it can still take
#guard (rq.1.listUnspents.map (·.pendingBlinded)).contains 2
def q1 : Wallet × PendingOp := (aliceBegin alice5 rq.2.1 [toProxy rq.2.2 100]).toOption.get!
def q1e : Wallet × World × List (String × Consignment) := aliceEnd q1 rq.2.1
def q2 : Wallet × PendingOp := (aliceBegin q1e.1 q1e.2.1 [toProxy rq.2.2 100]).toOption.get!
def q2e : Wallet × World × List (String × Consignment) := aliceEnd q2 q1e.2.1

-- two transfers to the invoice, by two operation keys, reach its quota
#guard (proxyOf q2e.2.1).invoiceCheck [iidQ] == [(iidQ, .full)] &&
  ((proxyOf q2e.2.1).transferList iidQ).map (·.length) == .ok 2
def bobQ : Refreshed := refreshed rq.1 q2e.2.1 bobO
-- the first transfer goes to the receive, the second gets an incoming transfer of its own
#guard (bobQ.1.db.transfers.filter (·.invoiceIdx.isSome)).length == 2
-- each keeps its data apart
#guard (bobQ.1.db.transfers.filterMap (·.receiveDir)).length == 2
-- each ACK releases its operation's transaction
#guard outcomes bobQ == [⟨some .waitingConfirmations, none⟩, ⟨some .waitingConfirmations, none⟩]
def aliceQ : Refreshed := refreshed q2e.1 bobQ.2.1 aliceO
-- Alice completes both sends
#guard outcomes aliceQ == [⟨some .waitingConfirmations, none⟩, ⟨some .waitingConfirmations, none⟩]
def bobQDone : Wallet := (refreshed bobQ.1 (mined aliceQ.2.1) bobO).1
-- Bob holds both payments
#guard bobQDone.assetBalance usdt == ⟨200, 200, 200⟩
-- the discovered transfer's path is one of the status machine
#guard validPath true [.waitingCounterparty, .waitingConfirmations, .settled]
/-- A receive of Bob's with quota `q` through `eps`: its recipient id or its error. -/
def quotaReceive (eps : List String) (q : Nat) : Result String :=
  (bob1.blindReceive wp none (.fungible 1) exp eps (online := some bobO) (quota := q)).map
    (·.2.2.recipientId)
-- a quota is at least 1
#guard quotaReceive [endpoint] 0 == .error (.invalidQuota "must be at least 1")
-- a reusable invoice needs proxies to keep its transfers apart
#guard quotaReceive [] 2 == .error (.invalidQuota "a reusable invoice requires transport endpoints")
-- a blind one needs a slot on its UTXO for each transfer it takes
#guard quotaReceive [endpoint] 6
  == .error (.invalidQuota "a blind invoice can receive at most 5 transfers")
/-- The most slots a UTXO of Bob's keeps at time `t`. -/
def slotsAt (t : Nat) : Nat :=
  ((rq.1.listUnspents (now := some t)).map (·.pendingBlinded)).foldl max 0
-- the invoice keeps both its slots until its deadline, then only its receive's
#guard slotsAt (exp + 86400 + 299) == 2 && slotsAt (exp + 86400 + 300) == 1

/-! ## An expired receive -/

-- before its expiration the receive can be cancelled
#guard (bobR.failTransfers wR bobO (some inv1.batchTransferIdx)).2.2 == .ok true
-- just past it, the proxies may still take a transfer: it is not expired yet
#guard (bobR.failTransfers (wR.setTime (exp + 1)) bobO).2.2 == .ok false
def bobRBatch : DbBatchTransfer := (bobR.db.batch? inv1.batchTransferIdx).getD default
-- it is not expired at exp + 1 only by the clock skew margin
#guard !bobRBatch.incomingExpired (exp + 1) && bobRBatch.isExpired (exp + 1) &&
  bobRBatch.incomingExpired (exp + 301)
-- so the error of the refresh before the fail is reported, not ignored as for an expired receive
#guard (bobR.failTransfers (wS.setTime (exp + 1)) bobO (some inv1.batchTransferIdx)).2.2
  == .error .operationExpired
-- past the clock skew margin too, with nothing pending on the proxy, it fails
def expired : Wallet × World × Result Bool := bobR.failTransfers (wR.setTime (exp + 301)) bobO
#guard expired.2.2 == .ok true && statusOf expired.1 inv1.batchTransferIdx == some .failed
-- its UTXO is free again
#guard (expired.1.listUnspents.filter (·.pendingBlinded > 0)).isEmpty

/-! ## Failing a send: the signed transaction is revoked -/

-- before any ACK, failing the send revokes its signed transaction on the sender proxy
def revoked : Wallet × World × Result Bool := aliceP.failTransfers wS aliceO (some sendIdx)
#guard revoked.2.2 == .ok true && statusOf revoked.1 sendIdx == some .failed
-- a failed send cannot be ended again: its revoked transaction does not come back
#guard (revoked.1.sendEnd revoked.2.1 aliceO begunP.2.txid).map (·.2.2.length)
  == .error (.cannotEndTransfer (toString begunP.2.txid))
-- the proxy's operation holds no signed transaction
#guard ((proxyOf revoked.2.1).operations.find? senderPk).map
  (·.transfers.values.all (·.signedTx.isNone)) == some true
-- Bob's ACK then gets no transaction back: he waits for a broadcast that never comes
def bobAfter : Refreshed := refreshed bobR revoked.2.1 bobO
#guard reported bobAfter inv1.batchTransferIdx == some ⟨some .waitingBroadcast, none⟩
-- a day past the broadcast deadline, his receive fails
#guard reported (refreshed bobAfter.1 (bobAfter.2.1.setTime (opExp + 2 * 86400 + 1)) bobO)
  inv1.batchTransferIdx == some ⟨some .failed, none⟩
-- once the operation expired unreleased, his next ACK fails the receive at once
#guard reported (refreshed bobAfter.1 (bobAfter.2.1.setTime (opExp + 1)) bobO)
  inv1.batchTransferIdx == some ⟨some .failed, none⟩
def failWB : Wallet × World × Result Bool :=
  bobAfter.1.failTransfers bobAfter.2.1 bobO (some inv1.batchTransferIdx)
-- before its confirmation deadline he cannot fail it: Alice may still broadcast
#guard failWB.2.2 == .error .cannotFailBatchTransfer &&
  statusOf failWB.1 inv1.batchTransferIdx == some .waitingBroadcast
-- after it he can
#guard (bobAfter.1.failTransfers (bobAfter.2.1.setTime (opExp + 2 * 86400 + 1)) bobO
  (some inv1.batchTransferIdx)).2.2 == .ok true
-- the receiver's path is one of the status machine
#guard validPath true [.waitingCounterparty, .waitingBroadcast, .failed]
-- a send not ended yet is unknown to its sender proxy: it fails
#guard (begunP.1.failTransfers wR aliceO (some (batchOf begunP.1 begunP.2.txid))).2.2 == .ok true
-- once Bob ACKed, the transaction is released: the fail refreshes the send instead
def tooLate : Wallet × World × Result Bool := aliceP.failTransfers bobRef.2.1 aliceO (some sendIdx)
#guard tooLate.2.2 == .error .cannotFailBatchTransfer
-- what the refresh did stays
#guard statusOf tooLate.1 sendIdx == some .waitingConfirmations

/-! ## Downloads that are not what was announced -/

def mallory : SecretKey := ⟨"mallory"⟩
/-- A post by Mallory to Bob's invoice of `file`, announced with `hash`. -/
def forged (file : Blob) (hash : String) : World :=
  let p := Proxy.ConsignmentPost.make mallory iid1 endpoint hash false file wR.now
  withServer wR ((proxyOf wR).consignmentPost p).toOption.get!
def anyConsignment : Consignment := (alice5.exportContract usdt).toOption.get!
def malloryKey : String := (deriveShared mallory inv1.publicKey).symKey

-- encrypted with another key: it does not decrypt, Bob refuses it
def undecryptable : Refreshed :=
  refreshed bobR (forged (Blob.encrypt (.consignment anyConsignment) "other key")
    (Payload.consignment anyConsignment).hash) bobO
#guard reported undecryptable inv1.batchTransferIdx == some ⟨some .failed, none⟩
-- announced with another hash than its plaintext's: Bob refuses it
def mismatch : Refreshed :=
  refreshed bobR (forged (Blob.encrypt (.consignment anyConsignment) malloryKey)
    (Payload.bytes "other").hash) bobO
#guard reported mismatch inv1.batchTransferIdx == some ⟨some .failed, none⟩
-- the refused transfer's data goes from the proxy
#guard ((proxyOf mismatch.2.1).transferList iid1).map (·.map (·.2)) == .ok [.retrieved]


/-! ## Spam and copies sent to the reusable invoice -/

def eve : SecretKey := ⟨"eve"⟩
/-- `w` with an undecryptable post by `k` to the reusable invoice. -/
def spamQ (w : World) (k : SecretKey) : World :=
  let p := Proxy.ConsignmentPost.make k iidQ endpoint (Payload.bytes "x").hash false
    (Blob.encrypt (.bytes "x") "other key") w.now
  withServer w ((proxyOf w).consignmentPost p).toOption.get!
def wSpam : World := spamQ (spamQ rq.2.1 mallory) eve
-- two posts take the invoice's quota
#guard (proxyOf wSpam).invoiceCheck [iidQ] == [(iidQ, .full)]
def bobSpam : Refreshed := refreshed rq.1 wSpam bobO
-- discovery refuses and deletes them: the invoice takes transfers again, the receive waits
#guard (proxyOf bobSpam.2.1).invoiceCheck [iidQ] == [(iidQ, .available)] &&
  outcomes bobSpam == [⟨none, none⟩]
/-- Alice's first transfer to the invoice, as Mallory reposts it with her own key. -/
def copyQ : Consignment := (q1e.2.2.headD default).2
def copied : World :=
  let key := (deriveShared mallory rq.2.2.publicKey).symKey
  let p := Proxy.ConsignmentPost.make mallory iidQ endpoint (Payload.consignment copyQ).hash false
    (Blob.encrypt (.consignment copyQ) key) q1e.2.1.now
  withServer q1e.2.1 ((proxyOf q1e.2.1).consignmentPost p).toOption.get!
def bobCopy : Refreshed := refreshed rq.1 copied bobO
-- the copy pays with the same transaction: it is refused, the payment credited once
#guard outcomes bobCopy == [⟨some .waitingConfirmations, none⟩, ⟨some .failed, none⟩] &&
  (bobCopy.1.assetBalance usdt).future == 100
-- the refused copy is deleted on the proxy
#guard ((proxyOf bobCopy.2.1).transferList iidQ).map (·.length) == .ok 1
def copyIdx : Nat := ((bobCopy.2.2.find? (·.2.updatedStatus == some .failed)).map (·.1)).getD 0
-- it stays while the invoice is live, and can go once its deadline passed
#guard (bobCopy.1.deleteTransfers bobCopy.2.1.now (some copyIdx)).map (·.2)
    == .error .cannotDeleteBatchTransfer &&
  (bobCopy.1.deleteTransfers (exp + 86400 + 300) (some copyIdx)).map (·.2) == .ok true
/-- Mallory's copy under a transfer id her key does not derive. -/
def misfiled : World :=
  let h := (Payload.consignment copyQ).hash
  let file := Blob.encrypt (.consignment copyQ) (deriveShared mallory rq.2.2.publicKey).symKey
  let tid := transferId iidQ eve.pk
  let p : Proxy.ConsignmentPost :=
    { invoiceId := iidQ, transferId := tid, senderTransportEndpoint := endpoint
      senderPk := mallory.pk, consignmentHash := h, batch := false, powTimestamp := rq.2.1.now
      powNonce := "0", file
      signature := signMessage mallory (Proxy.Msg.postConsignment tid h file.hash) }
  withServer rq.2.1 ((proxyOf rq.2.1).postConsignmentWithPow p).toOption.get!
-- discovery deletes it unread
#guard ((proxyOf (refreshed rq.1 misfiled bobO).2.1).transferList iidQ).map (·.length) == .ok 0
/-- Bob's reusable invoice for 10 USDT. -/
def rqU : Wallet × World × ReceiveData :=
  (bobKnows.blindReceive wp (some usdt) (.fungible 10) exp [endpoint] (online := some bobO)
    (quota := 2)).toOption.get!
def eurQ : Wallet × PendingOp :=
  (euro.1.sendBegin rqU.2.1 aliceO [(euro.2.id, [toProxy rqU.2.2 10])] false 1 1 opExp
    (some endpoint)).toOption.get!
def eurQe : Wallet × World × List (String × Consignment) := aliceEnd eurQ rqU.2.1
def bobEurQ : Refreshed := refreshed rqU.1 eurQe.2.1 bobO
-- a transfer of another asset is NACKed and deleted by discovery
#guard outcomes bobEurQ == [⟨none, none⟩] &&
  (proxyOf bobEurQ.2.1).transferList (invoiceId rqU.2.2.recipientId rqU.2.2.publicKey) == .ok []
-- Alice reads the NACK: her send fails
#guard reported (refreshed eurQe.1 bobEurQ.2.1 aliceO) (batchOf eurQe.1 eurQ.2.txid)
  == some ⟨some .failed, none⟩

/-! ## A sender proxy that cannot be trusted -/

/-- Bob's ACK on Alice's operation as a proxy serves it, forged with Mallory's signature. -/
def forgedAck : World :=
  let s := proxyOf wS
  let op := (s.operations.find? senderPk).getD default
  let r := (op.transfers.find? tidP).getD default
  let sig := signMessage mallory (Proxy.Msg.ack tidP true r.consignmentHash)
  let r' := { r with ack := some true, signature := some sig }
  let op' := { op with transfers := op.transfers.insert tidP r' }
  withServer wS { s with operations := s.operations.insert senderPk op' }
def aliceForged : Refreshed := refreshed aliceP forgedAck aliceO
-- the signature is not Bob's: the send keeps no ACK, broadcasts nothing and reports it
#guard reported aliceForged sendIdx
    == some ⟨none, some (reprStr Error.invalidContentSignature)⟩ &&
  (aliceForged.1.db.transfersOfBatch sendIdx).map (·.ack) == [none] &&
  (aliceForged.2.1.chain.findMempool? begunP.2.txid).isNone
-- nor can it be failed: the proxy may have released the transaction
#guard (aliceP.failTransfers forgedAck aliceO (some sendIdx)).2.2 == .error .cannotFailBatchTransfer
-- a day past its expiration the proxy drops the operation: Bob broadcast, the send completes
#guard reported (refreshed aliceP (bobRef.2.1.setTime (opExp + 86400 + 1)) aliceO) sendIdx
  == some ⟨some .waitingConfirmations, none⟩
def lostNoAck : World := wS.setTime (opExp + 86400 + 1)
-- never ACKed, it waits, reporting the lost operation, and cannot be failed
#guard reported (refreshed aliceP lostNoAck aliceO) sendIdx
    == some ⟨none, some (reprStr Error.operationNotFound)⟩ &&
  (aliceP.failTransfers lostNoAck aliceO (some sendIdx)).2.2 == .error .cannotFailBatchTransfer
-- past its broadcast deadline and the clock skew margin it fails
#guard reported (refreshed aliceP (wS.setTime (opExp + 86400 + 301)) aliceO) sendIdx
  == some ⟨some .failed, none⟩
-- a proxy that lost the operation before its expiration: the fail is denied
#guard (aliceP.failTransfers (withServer wS (Proxy.Server.init url wS.now)) aliceO
  (some sendIdx)).2.2 == .error .cannotFailBatchTransfer

/-! ## A released send near its invoice expiration -/

/-- Bob's released transaction gone from the mempool, his invoice about to expire. -/
def gone : World :=
  { bobRef.2.1 with chain := bobRef.2.1.chain.evict begunP.2.txid }.setTime (exp - 300)
def aliceGone : Refreshed := refreshed aliceP gone aliceO
-- Bob may have failed his receive: Alice does not broadcast
#guard reported aliceGone sendIdx == some ⟨none, none⟩ &&
  (aliceGone.2.1.chain.findMempool? begunP.2.txid).isNone
-- with the transaction on chain she completes
#guard reported (refreshed aliceP (bobRef.2.1.setTime (exp - 300)) aliceO) sendIdx
  == some ⟨some .waitingConfirmations, none⟩
/-- An input of Alice's send spent by another transaction, mined. -/
def inputSpent : World :=
  let tx := mkTx (begunP.2.tx.inputs.map (·.prevout)) [⟨500, .p2wpkh "elsewhere"⟩]
  { gone with chain := ((gone.chain.broadcast tx).toOption.getD gone.chain).mine }
-- with an input spent elsewhere she fails
#guard reported (refreshed aliceP inputSpent aliceO) sendIdx == some ⟨some .failed, none⟩

/-! ## Failing a send a proxy recipient already holds -/

/-- Bob's out-of-band receive next to his proxy invoice. -/
def oobR : Wallet × ReceiveData := received (bobR.blindReceive wR none (.fungible 100) exp)
def begunMix : Wallet × PendingOp :=
  (aliceBegin alice5 wR
    [toBobP, { recipientId := oobR.2.recipientId, assignment := .fungible 100 }]).toOption.get!
def endedMix : Wallet × World × List (String × Consignment) := aliceEnd begunMix wR
def mixIdx : Nat := batchOf endedMix.1 begunMix.2.txid
def bobMix : Refreshed := refreshed oobR.1 endedMix.2.1 bobO
-- Bob's ACK releases the transaction; Alice still waits for the out-of-band ACK
#guard (bobMix.2.1.chain.findMempool? begunMix.2.txid).isSome &&
  reported (refreshed endedMix.1 bobMix.2.1 aliceO) mixIdx == some ⟨none, none⟩
def failMix : Wallet × World × Result Bool :=
  endedMix.1.failTransfers bobMix.2.1 aliceO (some mixIdx)
-- failing it finds the transaction on chain: it completes instead
#guard failMix.2.2 == .error .cannotFailBatchTransfer &&
  statusOf failMix.1 mixIdx == some .waitingConfirmations
def failMixGone : Wallet × World × Result Bool :=
  endedMix.1.failTransfers { bobMix.2.1 with chain := bobMix.2.1.chain.evict begunMix.2.txid }
    aliceO (some mixIdx)
-- with it gone from the mempool the proxy reports it released: the fail is denied
#guard failMixGone.2.2 == .error .cannotFailBatchTransfer &&
  statusOf failMixGone.1 mixIdx == some .waitingCounterparty

/-! ## Ending a send: expirations and refused posts -/

-- never registered, the send cannot end after its expiration: the proxy refuses it
#guard (begunP.1.sendEnd (wR.setTime (opExp + 1)) aliceO begunP.2.txid).map (·.2.2.length)
  == .error .expirationInvalid
-- registered already, it ends again: nothing is posted, it waits for the ACK
#guard (aliceP.sendEnd (wS.setTime (opExp + 1)) aliceO begunP.2.txid).map
    (fun (w, _, _) => statusOf w sendIdx) == .ok (some .waitingCounterparty)
def sndUrl : String := "http://sender.test/json-rpc"
def sndEndpoint : String := "rpc://sender.test/json-rpc"
/-- The world with a sender proxy of its own. -/
def wSnd : World := wR.withProxy (Proxy.Server.init sndUrl world2.now)
def begunS : Wallet × PendingOp :=
  (aliceBegin alice5 wSnd [toBobP] (senderEndpoint := some sndEndpoint)).toOption.get!
def endedS : Wallet × World × List (String × Consignment) := aliceEnd begunS wSnd
def wDrained : World :=
  withServer wSnd ((proxyOf wSnd).configure fun c => { c with draining := true })
-- the only recipient proxy drains after the begin: the end reports it
#guard (begunS.1.sendEnd wDrained aliceO begunS.2.txid).map (·.2.2.length)
  == .error .proxyDraining
def firstEnd : Result (Wallet × List (String × Consignment)) × World :=
  (begunS.1.sendEndStep begunS.2.txid).exec wDrained
-- that end registered the operation before the refusal
#guard (proxyOf firstEnd.2 sndUrl).operations.size == 1
def againEnd : Result (Wallet × World × List (String × Consignment)) :=
  let s := (proxyOf firstEnd.2).configure fun c => { c with draining := false }
  let w := withServer firstEnd.2 s
  begunS.1.sendEnd (w.setTime (opExp + 1)) aliceO begunS.2.txid
-- ended again after its expiration, it posts nothing and waits for the ACK
#guard (againEnd.map fun (w, _, _) => statusOf w (batchOf w begunS.2.txid))
    == .ok (some .waitingCounterparty) &&
  (againEnd.map fun (_, w, _) => (proxyOf w).transferList iid1) == .ok (.ok [])
/-- A world where Bob's invoice is reserved on two proxies. -/
def wTwo : World :=
  (wp.withProxy (Proxy.Server.init shortUrl world2.now)).withProxy
    (Proxy.Server.init sndUrl world2.now)
def rTwo : Wallet × World × ReceiveData :=
  (bob1.blindReceive wTwo none (.fungible 600) exp [endpoint, shortEndpoint]
    (online := some bobO)).toOption.get!
def begunTwo : Wallet × PendingOp :=
  (aliceBegin alice5 rTwo.2.1
    [{ toProxy rTwo.2.2 600 with transportEndpoints := [endpoint, shortEndpoint] }]
    (senderEndpoint := some sndEndpoint)).toOption.get!
/-- The endpoints of the send's transfer after an end with the first proxy draining. -/
def twoEndpoints : Result (List (String × Bool)) :=
  let w := withServer rTwo.2.1 ((proxyOf rTwo.2.1).configure fun c => { c with draining := true })
  (begunTwo.1.sendEnd w aliceO begunTwo.2.txid).map fun (a, _, _) =>
    let t := (a.db.transfersOfBatch (batchOf a begunTwo.2.txid)).headD default
    (a.db.endpointsOf t.idx).map fun e => (e.endpoint, e.used)
-- the second proxy takes the consignment
#guard twoEndpoints == .ok [(url, false), (shortUrl, true), (sndUrl, false)]
/-- Mallory's junk on Bob's invoice under the transfer id of Alice's send. -/
def squat : World :=
  let file := Blob.encrypt (.bytes "junk") "k"
  let h := (Payload.bytes "junk").hash
  let p : Proxy.ConsignmentPost :=
    { invoiceId := iid1, transferId := tidP, senderTransportEndpoint := endpoint
      senderPk := mallory.pk, consignmentHash := h, batch := false, powTimestamp := wR.now
      powNonce := "0", file
      signature := signMessage mallory (Proxy.Msg.postConsignment tidP h file.hash) }
  withServer wR ((proxyOf wR).postConsignmentWithPow p).toOption.get!
-- Alice's post cannot replace it: her end fails
#guard (begunP.1.sendEnd squat aliceO begunP.2.txid).map (·.2.2.length)
  == .error (.proxyCannotChange "Cannot change: sender_pk, consignment_hash, file")
-- Bob ignores a transfer whose id does not derive from its sender's key
#guard reported (refreshed bobR squat bobO) inv1.batchTransferIdx == some ⟨none, none⟩

/-! ## A download kept after a failed refresh -/

/-- `w` without the proxy at `u`. -/
def without (w : World) (u : String) : World := { w with proxies := w.proxies.filter (·.1 != u) }
def bobNoSender : Refreshed := refreshed bobR (without endedS.2.1 sndUrl) bobO
-- Bob downloads and validates, then cannot reach the sender proxy: the refresh fails
#guard reported bobNoSender inv1.batchTransferIdx
  == some ⟨none, some (reprStr (ProxyClient.unreachable sndUrl))⟩
/-- The sender proxy back, the recipient proxy gone. -/
def senderBack : World :=
  let w := without bobNoSender.2.1 url
  { w with proxies := w.proxies ++ [(sndUrl, proxyOf endedS.2.1 sndUrl)] }
-- the download his files kept is processed and ACKed without the recipient proxy
#guard reported (refreshed bobR senderBack bobO) inv1.batchTransferIdx
  == some ⟨some .waitingConfirmations, none⟩

/-! ## An expired blind receive with a transfer pending -/

/-- The world of Alice's send at `t`, its sender proxy not answering. -/
def senderGone (t : Nat) : World := (without endedS.2.1 sndUrl).setTime t
-- past the expiration a transfer pending on his proxy keeps Bob's UTXO: he cannot ACK it yet
#guard (bobR.failTransfers (senderGone (exp + 301)) bobO).2.2 == .ok false &&
  (bobR.failTransfers (senderGone (exp + 301)) bobO (some inv1.batchTransferIdx)).2.2
    == .error .cannotFailBatchTransfer
-- with no proxy answering it waits for the retention deadline, then fails
#guard (bobR.failTransfers ((without wR url).setTime (exp + 301)) bobO).2.2 == .ok false &&
  (bobR.failTransfers ((without wR url).setTime (exp + 86400 + 301)) bobO).2.2 == .ok true

/-! ## An answer already on the sender proxy -/

def bobSeed : String :=
  ((bobR.db.batch? inv1.batchTransferIdx).bind (·.operationSecretKey)).getD ""
/-- `w` with Bob's answer to the transfer `tid` of hash `h` on the proxy at `u`, as a refresh
whose result was lost posted it. -/
def answered (w : World) (u tid h : String) (ack : Bool) : World :=
  let s := proxyOf w u
  let posted := s.ackPost tid ack (Proxy.ackSignature ⟨bobSeed⟩ tid ack h)
  withServer w ((posted.map (·.1)).toOption.getD s)
def bobNacked : Refreshed :=
  refreshed bobR (answered wS url tidP (sentRow.consignmentHash.getD "") false) bobO
-- his NACK is recorded: his ACK is refused, he fails, recording no ACK
#guard reported bobNacked inv1.batchTransferIdx == some ⟨some .failed, none⟩ &&
  (bobNacked.1.db.transfersOfBatch inv1.batchTransferIdx).map (·.ack) == [none]
def tidG : String := transferId iid1 (SecretKey.pk ⟨begunG.2.operationSecretKey.getD ""⟩)
def hashG : String :=
  let t := (endedG.1.db.transfersOfBatch (batchOf endedG.1 begunG.2.txid)).headD default
  t.consignmentHash.getD ""
-- his ACK is recorded where the grace is too short: his NACK is refused, he still fails
#guard reported (refreshed bobR (answered endedG.2.1 shortUrl tidG hashG true) bobO)
  inv1.batchTransferIdx == some ⟨some .failed, none⟩

/-! ## Expirations a sender proxy answers -/

-- a deadline counts from an answered expiration that is neither past nor after the invoice's
#guard ProxyClient.broadcastDeadline (some (toString opExp)) 86400 (some exp) wR.now
    == some (opExp + 86400) &&
  ProxyClient.broadcastDeadline (some (toString (exp + 1))) 86400 (some exp) wR.now == none &&
  ProxyClient.broadcastDeadline (some (toString (wR.now - 1))) 86400 (some exp) wR.now == none &&
  ProxyClient.broadcastDeadline (some "soon") 86400 (some exp) wR.now == none &&
  ProxyClient.broadcastDeadline (some (toString opExp)) 86400 none wR.now == none
/-- Alice registering her operation herself, expiring after the invoice, then posting. -/
def hostile : World :=
  let sk : SecretKey := ⟨begunP.2.operationSecretKey.getD ""⟩
  let c := (endedP.2.2.headD default).2
  let h := (Payload.consignment c).hash
  let td := [(tidP, Proxy.AckTransferData.make sk inv1.publicKey h begunP.2.tx)]
  let prep : Proxy.AckPrepare := { transferData := td, expiresAt := exp + 1000
                                   signedTxHash := (Payload.tx begunP.2.tx).hash
                                   senderPk := sk.pk }
  let s := ((proxyOf wR).ackPrepare prep).toOption.get!
  let file := Blob.forRecipient .required (deriveShared sk inv1.publicKey).symKey (.consignment c)
  let post := Proxy.ConsignmentPost.make sk iid1 endpoint h false file wR.now
  withServer wR (s.postConsignmentWithPow post).toOption.get!
def bobHostile : Refreshed := refreshed bobR hostile bobO
-- Bob ACKs and broadcasts but takes no deadline from it: his receive expires with the invoice
#guard reported bobHostile inv1.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩ &&
  (bobHostile.1.db.batch? inv1.batchTransferIdx).bind (·.broadcastDeadline) == none

/-! ## A receiver that does not support encryption -/

def rU : Wallet × World × ReceiveData :=
  (bob1.blindReceive wp none (.fungible 600) exp [endpoint] (online := some bobO)
    (encryption := some .unsupported)).toOption.get!
def begunU : Wallet × PendingOp :=
  (aliceBegin alice5 rU.2.1 [{ toProxy rU.2.2 600 with encryption := .unsupported }]).toOption.get!
def endedU : Wallet × World × List (String × Consignment) := aliceEnd begunU rU.2.1
def tidU : String := transferId (invoiceId rU.2.2.recipientId rU.2.2.publicKey)
  (SecretKey.pk ⟨begunU.2.operationSecretKey.getD ""⟩)
-- Alice posts the consignment in clear, as the invoice asks
#guard (((proxyOf endedU.2.1).transfers.find? tidU).bind (·.consignment)) matches some (.plain _)
-- Bob reads it in clear and ACKs
#guard reported (refreshed rU.1 endedU.2.1 bobO) rU.2.2.batchTransferIdx
  == some ⟨some .waitingConfirmations, none⟩

/-! ## Unsafe history received through the proxy -/

/-- The safe height world, Carol holding 300 unconfirmed, with the proxy and a short-grace one. -/
def wCarol : World :=
  (SafeHeightScenario.wC2.withProxy (Proxy.Server.init url SafeHeightScenario.wC2.now)).withProxy
    (Proxy.Server.init shortUrl SafeHeightScenario.wC2.now 3600)
def rCarol : Wallet × World × ReceiveData := bobReceive bob1 wCarol 100
/-- Carol's send of 100 to Bob's invoice, its sender proxy at `se`. -/
def carolEnds (se : String) : Wallet × PendingOp × World :=
  let b := (SafeHeightScenario.carolSettled.sendBegin rCarol.2.1 SafeHeightScenario.carolO
    [(usdt, [toProxy rCarol.2.2 100])] false 1 1 opExp (some se)).toOption.get!
  let e := (b.1.sendEnd rCarol.2.1 SafeHeightScenario.carolO b.2.txid).toOption.get!
  (e.1, b.2, e.2.1)
def carolC : Wallet × PendingOp × World := carolEnds endpoint
def bobC : Refreshed := refreshed rCarol.1 carolC.2.2 bobO
-- her history is not mined: Bob waits for the safe height without ACKing
#guard reported bobC rCarol.2.2.batchTransferIdx == some ⟨some .waitingSafeHeight, none⟩
def tidC : String := transferId (invoiceId rCarol.2.2.recipientId rCarol.2.2.publicKey)
  (SecretKey.pk ⟨carolC.2.1.operationSecretKey.getD ""⟩)
def bobCSafe : Refreshed := refreshed bobC.1 (mined bobC.2.1) bobO
-- once it is mined he ACKs on the sender proxy and broadcasts the released transaction
#guard reported bobCSafe rCarol.2.2.batchTransferIdx
    == some ⟨some .waitingConfirmations, none⟩ &&
  (bobCSafe.2.1.chain.findMempool? carolC.2.1.txid).isSome &&
  ((proxyOf bobCSafe.2.1).ackGet [tidC]).map (·.acks) == .ok [(tidC, true)]
-- Carol completes
#guard reported (refreshed carolC.1 bobCSafe.2.1 SafeHeightScenario.carolO)
  (batchOf carolC.1 carolC.2.1.txid) == some ⟨some .waitingConfirmations, none⟩
def carolShort : Wallet × PendingOp × World := carolEnds shortEndpoint
def bobCS : Refreshed := refreshed rCarol.1 carolShort.2.2 bobO
-- with a sender proxy keeping a released transaction an hour only, he NACKs once safe
#guard reported bobCS rCarol.2.2.batchTransferIdx == some ⟨some .waitingSafeHeight, none⟩ &&
  reported (refreshed bobCS.1 (mined bobCS.2.1) bobO) rCarol.2.2.batchTransferIdx
    == some ⟨some .failed, none⟩
#guard validPath true [.waitingCounterparty, .waitingSafeHeight, .failed]

/-! ## Legacy transfers -/

/-- `w` with the batch `bi` saved as a legacy transfer, without an operation key. -/
def legacy (w : Wallet) (bi : Nat) : Wallet :=
  { w with db := w.db.updateBatch bi fun b =>
      { b with operationSecretKey := none, broadcastDeadline := none } }
-- one waiting for its counterparty fails
#guard reported (refreshed (legacy bob2 invoice.batchTransferIdx) world2 bobO)
  invoice.batchTransferIdx == some ⟨some .failed, none⟩
-- one waiting for the broadcast fails once expired
#guard reported (refreshed (legacy bobB.1 rb1.2.2.batchTransferIdx)
    ({ bobB.2.1 with chain := bobB.2.1.chain.evict begunB.2.txid }.setTime (exp + 1)) bobO)
  rb1.2.2.batchTransferIdx == some ⟨some .failed, none⟩

/-! ## An expired reusable invoice keeps no slot -/

def infIssued : Wallet × DbAsset :=
  (alice5.issueAssetIfa world2.now "INF" "Inflatable" 0 [100] []).toOption.get!
def infQ : Wallet × PendingOp :=
  (infIssued.1.sendBegin rq.2.1 aliceO [(infIssued.2.id, [toProxy rq.2.2 100])] false 1 1 opExp
    (some endpoint)).toOption.get!
def infQe : Wallet × World × List (String × Consignment) := aliceEnd infQ rq.2.1
def bobInfQ : Refreshed := refreshed rq.1 infQe.2.1 bobO
def bobInf : Refreshed :=
  refreshed bobInfQ.1 (mined (refreshed infQe.1 bobInfQ.2.1 aliceO).2.1) bobO
/-- Bob's burn of the 100 he received, at time `t`. -/
def burnAt (t : Nat) : Result Txid :=
  (bobInf.1.burn (bobInf.2.1.setTime t) bobO infIssued.2.id 100).map (·.2.2)
-- while the invoice is live its UTXO keeps a slot for a second transfer: the 100 stay
#guard burnAt (exp + 86400 + 299) matches .error (.insufficientAssignments _ _)
-- once its deadline passed the slot goes: the burn spends them
#guard burnAt (exp + 86400 + 300) matches .ok _

end Rgb.Examples.ProxyTransferScenario
