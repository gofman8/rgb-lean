import Rgb.Lib.Mint
import Rgb.Examples.ProxyTransfer

/-!
# Mints

Alice issues a BFA asset with three mint rights, bridged on EVM chain 1, whose wallets allow a
mint lock between 5 and 100 blocks after the latest block. Bob reserves a blind invoice for 500
on the proxy. Alice begins a mint of 500 to it, its lock to be included before bridge block 80:
the transfer is initiated and the consignment waits on the proxy. Bob's refresh checks the mint
and saves the lock to make; his consignment then waits for the lock. The lock is included at
block 52, then finalized: Alice's `mint_end` broadcasts and Bob accepts the mint; both settle
once a block confirms it. Then the checks of a begin, an expired lock, `fail_transfers` on a
pending mint, the mints a receiver refuses, mints to invoices asking for no amount, a checked mint
whose inputs are spent elsewhere and mint rights moved by a send.
-/

namespace Rgb.Examples.MintScenario

open Rgb Rgb.Lib Rgb.Lib.Evm Rgb.Lib.ProxyCrypto Rgb.Examples.WalletScenario
  Rgb.Examples.TransferScenario Rgb.Examples.ProxyTransferScenario

/-! ## The bridge's chain -/

def bridgeHex : String := "0x" ++ rep 'b' 40
def bridgeAddress : EvmAddress := ⟨List.replicate 20 0xbb⟩
def evmUrl : String := "https://evm.test"

/-- EVM chain 1 at block `latest`, finalized at `fin`, its bridge holding `locks` and accounting
`supply` in circulation. -/
def ledgerAt (latest fin : Nat) (locks : List LockRecord := []) (supply : Nat := 0) : EvmLedger :=
  { chainId := 1, latest, finalized := fin
    accounts := [{ address := bridgeAddress, code := .bridge locks supply }] }

/-- The world with the bridge's chain in state `l`. -/
def withLedger (w : World) (l : EvmLedger) : World := { w with evm := [(evmUrl, l)] }

/-- A mint lock is included 5 to 100 blocks after the latest block of chain 1. -/
def chains : List (Nat × EvmChain) := [(1, ⟨evmUrl, 5, 100⟩)]

def wm0 : World := withLedger wp (ledgerAt 50 45)

/-! ## A BFA issuance with several mint rights -/

def issuedB : Wallet × DbAsset :=
  (alice5.issueAssetBfa wm0.now "₿TC" "Bridged" 0 3 1 bridgeHex).toOption.get!
def bfa : String := issuedB.2.id
def onA : Wallet × Online × Result Unit := issuedB.1.goOnline wm0 (evmChains := chains)
def aliceM : Wallet := onA.1
def aliceMO : Online := onA.2.1
def onB : Wallet × Online × Result Unit := bob1.goOnline wm0 (evmChains := chains)
def bobM : Wallet := onB.1
def bobMO : Online := onB.2.1

/-- The mint rights a wallet holds settled. -/
def rights (w : Wallet) : Nat :=
  ((w.listUnspents.flatMap (·.rgbAllocations)).filter fun a =>
    a.assetId == some bfa && a.assignment == .mintRight && a.settled).length

-- three mint rights on three UTXOs; a BFA asset issues nothing at genesis
#guard rights aliceM == 3 && aliceM.assetBalance bfa == ⟨0, 0, 0⟩
-- both wallets went online with the bridge's chain
#guard onA.2.2 == .ok () && onB.2.2 == .ok ()

/-- A blind invoice of Bob for `n` through the proxy. -/
def bobInvoice (w : Wallet) (world : World) (n : UInt64) : Wallet × World × ReceiveData :=
  (w.blindReceive world none (.fungible n) (world.now + 86400) [endpoint]
    (online := some bobMO)).toOption.get!

/-- Alice's mint of `n` to a receive: proxy endpoints and key, no expiration. -/
def toMint (d : ReceiveData) (n : UInt64) : Recipient :=
  { recipientId := d.recipientId, assignment := .fungible n, transportEndpoints := [endpoint]
    publicKey := some d.publicKey }

/-- Alice's mint begin of `r` with its lock before block `bb`. -/
def mintBy (w : Wallet) (world : World) (r : Recipient) (bb : Nat) :
    Result (Wallet × World × Wallet.MintBeginResult) :=
  w.mintBegin world aliceMO bfa r bb 1 1 endpoint

/-- The error of a mint begin, if any. -/
def beginError (r : Result (Wallet × World × Wallet.MintBeginResult)) : Option Error :=
  match r with
  | .error e => some e
  | .ok _ => none

/-! ## The checks of a begin -/

def rcv1 : Wallet × World × ReceiveData := bobInvoice bobM wm0 500
def bobR1 : Wallet := rcv1.1
def wm1 : World := rcv1.2.1
def inv : ReceiveData := rcv1.2.2

-- a schema without mints
#guard beginError (aliceM.mintBegin wm1 aliceMO usdt (toMint inv 500) 80 1 1 endpoint)
  == some (.unsupportedMint .nia)
-- a mint pays an amount
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with assignment := .mintRight } 80)
  == some .invalidAssignment
-- a fee rate under the minimum
#guard beginError (aliceM.mintBegin wm1 aliceMO bfa (toMint inv 500) 80 0 1 endpoint)
  == some (.invalidFeeRate "value under minimum 1")
-- a mint recipient is a proxy recipient
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with transportEndpoints := [] } 80)
  == some (.invalidTransportEndpoints "no valid transport endpoints")
-- a mint expires by its lock, so its recipient has no expiration
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with expirationTimestamp := some wm1.now } 80)
  == some (.invalidRecipientData "a mint recipient cannot have an expiration")
-- a zero amount
#guard beginError (mintBy aliceM wm1 (toMint inv 0) 80) == some .invalidAmountZero
-- a proxy that does not answer is not usable
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with
    transportEndpoints := ["rpc://down.test/json-rpc"] } 80)
  == some (.invalidTransportEndpoints "no valid transport endpoints")
-- the recipient is checked before the bridge's chain
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with transportEndpoints := [] } 51)
  == some (.invalidTransportEndpoints "no valid transport endpoints")
-- without an RPC URL for the bridge's chain (online without EVM chains)
#guard beginError (issuedB.1.mintBegin wm1 aliceO bfa (toMint inv 500) 80 1 1 endpoint)
  == some (.noEvmRpcUrl 1)
-- the latest block is 50: the lock needs a block between it and the one it commits to
#guard beginError (mintBy aliceM wm1 (toMint inv 500) 51) == some (.invalidBeforeBlock
  "the lock cannot be included before block 51, the latest external chain block being 50")
-- at least `min_mint_lock_blocks` after the latest block
#guard beginError (mintBy aliceM wm1 (toMint inv 500) 54) == some (.invalidBeforeBlock
  "block 54 is less than 5 blocks after the latest external chain block 50")
-- at most `max_mint_lock_blocks` after it
#guard beginError (mintBy aliceM wm1 (toMint inv 500) 151) == some (.invalidBeforeBlock
  "block 151 is more than 100 blocks after the latest external chain block 50")
-- both bounds are included
#guard beginError (mintBy aliceM wm1 (toMint inv 500) 55) == none &&
  beginError (mintBy aliceM wm1 (toMint inv 500) 150) == none

/-! ## The mint begins -/

def m1 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy aliceM wm1 (toMint inv 500) 80).toOption.get!
def aliceB1 : Wallet := m1.1
def wm2 : World := m1.2.1
def mintIdx : Nat := m1.2.2.batchTransferIdx
def mintOp : PendingOp := m1.2.2.op
def mintOpid : OpId := m1.2.2.opid
def mintKey : String := (⟨mintOp.operationSecretKey.getD ""⟩ : SecretKey).pk
def invId : String := invoiceId inv.recipientId inv.publicKey
def mintTid : String := transferId invId mintKey
/-- The mint transition the begin built. -/
def mintT : Transition :=
  ((mintOp.fascia.bind fun f => (f.bundles.toList.flatMap (·.2.knownTransitions)).find?
    (·.opid == mintOpid)).map (·.transition)).getD default

-- the mint is saved as initiated, as a mint
#guard aliceB1.transferStatuses bfa |>.contains (mintIdx, .initiated, .mint)
-- it spends one mint right, records the amount as issued and commits to block 80
#guard mintT.transitionType == Schemas.tsMint && mintT.inputs.length == 1 &&
  mintT.globals.find? Schemas.gsIssuedSupply == some [⟨.amount 500⟩] &&
  mintT.metadata.find? Schemas.msBeforeBlock == some ⟨.blockNumber ⟨80⟩⟩
-- the consignment waits on the recipient's proxy before the transaction is signed
#guard (proxyOf wm2).transferList invId == .ok [(mintTid, .pending)]
-- no operation is registered on the sender proxy: the recipient does not ACK a mint
#guard (proxyOf wm2).operations.isEmpty
def mintRow : DbTransfer := (aliceB1.db.transfersOfBatch mintIdx).headD default
-- the begin keeps the endpoints it posted to unused
#guard (aliceB1.db.endpointsOf mintRow.idx).map (fun e => (e.endpoint, e.kind, e.used))
  == [(url, .recipientProxy, false), (url, .senderProxy, false)]
-- the recipient row: the requested amount, no expiration
#guard mintRow.requestedAssignment == some (.fungible 500) && mintRow.invoiceExpiration == none
-- the mint right it spends is reserved
#guard aliceB1.db.reservedColored == mintOp.tx.inputs.map (·.prevout)
-- the invoice took the mint: a second one to it cannot be posted, so it does not begin
#guard beginError (mintBy aliceB1 wm2 (toMint inv 500) 80) == some .invoiceQuotaExceeded
-- nor one to an invoice never reserved
#guard beginError (mintBy aliceM wm1 { toMint inv 500 with publicKey := some (rep 'a' 64) } 80)
  == some .invoiceNotReserved

/-! ## The lock is not recorded yet -/

def end0 : Wallet × World × Result OperationResult := aliceB1.mintEnd wm2 aliceMO mintOp.txid

-- the mint cannot end without its lock
#guard end0.2.2 == .error (.mintLockNotFound (toString mintOpid))
-- it stays initiated
#guard statusOf end0.1 mintIdx == some .initiated
def toBobOob : Recipient := { recipientId := inv.recipientId, assignment := .fungible 100 }
def sendOp : Wallet × PendingOp :=
  (aliceB1.sendBegin wm2 aliceMO [(usdt, [toBobOob])] false 1 1 (wm2.now + 3600)).toOption.get!
-- another operation cannot be ended as a mint
#guard (sendOp.1.mintEnd wm2 aliceMO sendOp.2.txid).2.2
  == .error (.wrongOperation (toString sendOp.2.txid))
-- nor a mint as a send
#guard (aliceB1.sendEnd wm2 aliceMO mintOp.txid).map (·.2.2.length)
  == .error (.wrongOperation (toString mintOp.txid))

/-! ## The receiver checks the mint -/

def bobC1 : Refreshed := refreshed bobR1 wm2 bobMO
/-- The lock Bob checked: what has to be locked. -/
def lockM : LockId := LockId.of mintOpid mintOp.txid

-- the consignment waits for its lock: no status change
#guard reported bobC1 inv.batchTransferIdx == some ⟨none, none⟩
-- the mint is checked: the lock id, amount and block to make the lock with
#guard bobC1.1.getReceivedMint inv.recipientId ==
  [⟨toString mintOpid, lockM, 500, 80, 1, addressText bridgeAddress⟩]
-- the locks it waits for are saved
#guard (bobC1.1.mintLocks.map fun (_, p) => p.claims.map (·.lockId)) == [[lockM]]
-- nothing is received yet
#guard bobC1.1.assetBalance bfa == ⟨0, 0, 0⟩ && (bobC1.1.db.asset? bfa).isNone
-- a checked received mint cannot be failed: it expires by its lock only
#guard (bobC1.1.failTransfers bobC1.2.1 bobMO (some inv.batchTransferIdx)).2.2
  == .error .cannotFailBatchTransfer
def failFirst : Wallet × World × Result Bool :=
  bobR1.failTransfers wm2 bobMO (some inv.batchTransferIdx)
-- nor before any refresh: the refresh inside the fail checks it
#guard failFirst.2.2 == .error .cannotFailBatchTransfer &&
  statusOf failFirst.1 inv.batchTransferIdx == some .waitingCounterparty &&
  (failFirst.1.getReceivedMint inv.recipientId).length == 1

/-! ## The lock is included, then finalized -/

def wLocked : World := withLedger bobC1.2.1 (ledgerAt 55 50 [⟨lockM, 500, 52⟩] 500)

-- included at block 52, not finalized: the mint still cannot end
#guard (aliceB1.mintEnd wLocked aliceMO mintOp.txid).2.2
  == .error (.mintLockNotFound (toString mintOpid))
def bobC2 : Refreshed := refreshed bobC1.1 wLocked bobMO
-- the receiver waits while the lock is not confirmed
#guard reported bobC2 inv.batchTransferIdx == some ⟨none, none⟩

def wFinal : World := withLedger bobC2.2.1 (ledgerAt 60 55 [⟨lockM, 500, 52⟩] 500)
def bobC3 : Refreshed := refreshed bobC2.1 wFinal bobMO

-- once finalized the receiver accepts the mint: it waits for the minter's broadcast
#guard reported bobC3 inv.batchTransferIdx == some ⟨some .waitingBroadcast, none⟩
-- it posted no ACK
#guard (proxyOf bobC3.2.1).operations.isEmpty
-- the asset is known, with its bridge and the supply the bridge accounts
#guard ((bobC3.1.db.asset? bfa).map fun a =>
    (a.ticker, a.bridgeLocation, a.knownCirculatingSupply))
  == some (some "₿TC", some (.evm ⟨1, bridgeAddress⟩), some 500)
-- the 500 are pending in
#guard bobC3.1.assetBalance bfa == ⟨0, 500, 0⟩
-- the proxy may drop the consignment
#guard (proxyOf bobC3.2.1).transferList invId == .ok [(mintTid, .retrieved)]

def ended1 : Wallet × World × Result OperationResult :=
  aliceB1.mintEnd bobC3.2.1 aliceMO mintOp.txid
def aliceE1 : Wallet := ended1.1
def wm3 : World := ended1.2.1

-- the lock is confirmed: the mint ends
#guard ended1.2.2.map (·.txid) == .ok mintOp.txid
-- it waits for confirmations
#guard statusOf aliceE1 mintIdx == some .waitingConfirmations
-- its transaction is broadcast
#guard (wm3.chain.findMempool? mintOp.txid).isSome
-- the minter's known circulating supply is the bridge's
#guard (aliceE1.db.asset? bfa).bind (·.knownCirculatingSupply) == some 500
-- an ended mint cannot end again
#guard (aliceE1.mintEnd wm3 aliceMO mintOp.txid).2.2
  == .error (.cannotEndTransfer (toString mintOp.txid))

/-! ## Both settle after mining -/

def bobC4 : Refreshed := refreshed bobC3.1 wm3 bobMO
-- the receiver sees the transaction unconfirmed
#guard reported bobC4 inv.batchTransferIdx == some ⟨some .waitingConfirmations, none⟩
def wm4 : World := mined bobC4.2.1
def bobDoneM : Refreshed := refreshed bobC4.1 wm4 bobMO
def aliceDoneM : Refreshed := refreshed aliceE1 bobDoneM.2.1 aliceMO

-- a block confirms the mint: both transfers are settled
#guard statusOf bobDoneM.1 inv.batchTransferIdx == some .settled &&
  statusOf aliceDoneM.1 mintIdx == some .settled
-- Bob holds the 500 minted
#guard bobDoneM.1.assetBalance bfa == ⟨500, 500, 500⟩
-- Alice holds no asset, two mint rights left
#guard aliceDoneM.1.assetBalance bfa == ⟨0, 0, 0⟩ && rights aliceDoneM.1 == 2
-- both know the circulating supply the bridge accounts
#guard ((bobDoneM.1.listAssets [.bfa]).map (·.knownCirculatingSupply)) == [500] &&
  ((aliceDoneM.1.listAssets [.bfa]).map (·.knownCirculatingSupply)) == [500]
-- the sender's and the receiver's paths are of the status machine
#guard validPath false [.initiated, .waitingConfirmations, .settled] &&
  validPath true [.waitingCounterparty, .waitingBroadcast, .waitingConfirmations, .settled]

/-! ## A mint in the history of a transfer received out of band -/

/-- Alice online without EVM chains, with an out-of-band receive of 100. -/
def aliceNoChains : Wallet × Online × Result Unit := issuedB.1.goOnline wm4
def aliceRcv : Wallet × ReceiveData :=
  received (aliceNoChains.1.blindReceive wm4 none (.fungible 100) (wm4.now + 86400))
/-- Bob's send of 100 of the minted asset to it. -/
def bobToAlice : Wallet × World × List (String × Consignment) :=
  let r : Recipient := { recipientId := aliceRcv.2.recipientId, assignment := .fungible 100 }
  let b := (bobDoneM.1.sendBegin wm4 bobMO [(bfa, [r])] false 1 1 (wm4.now + 3600)).toOption.get!
  (b.1.sendEnd wm4 bobMO b.2.txid).toOption.get!
-- the mint's lock cannot be checked without an RPC URL: the receive waits, its status unchanged
#guard ((aliceRcv.1.provideOutOfBandConsignment bobToAlice.2.1 aliceNoChains.2.1
    (bobToAlice.2.2.headD default).2).map (·.2.2))
  == .ok [(aliceRcv.2.batchTransferIdx, ⟨none, none⟩)]

/-! ## An expired lock -/

def rcv2 : Wallet × World × ReceiveData := bobInvoice bobDoneM.1 aliceDoneM.2.1 500
def m2 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy aliceDoneM.1 rcv2.2.1 (toMint rcv2.2.2 500) 65).toOption.get!
def mint2Idx : Nat := m2.2.2.batchTransferIdx

-- with one mint right left among those it could spend, a mint is refused
#guard beginError (mintBy m2.1 m2.2.1 (toMint rcv2.2.2 500) 70) == some .lastMintRight
-- the fee rate is checked before the mint rights
#guard beginError (m2.1.mintBegin m2.2.1 aliceMO bfa (toMint rcv2.2.2 500) 70 0 1 endpoint)
  == some (.invalidFeeRate "value under minimum 1")
def bobX1 : Refreshed := refreshed rcv2.1 m2.2.1 bobMO
-- the receiver checks the second mint and waits for its lock
#guard reported bobX1 rcv2.2.2.batchTransferIdx == some ⟨none, none⟩ &&
  (bobX1.1.getReceivedMint rcv2.2.2.recipientId).length == 1

/-- Block 64 is finalized without the lock: it cannot be included before block 65. -/
def wExp : World := withLedger bobX1.2.1 (ledgerAt 69 64 [⟨lockM, 500, 52⟩] 500)
def end2 : Wallet × World × Result OperationResult :=
  m2.1.mintEnd wExp aliceMO m2.2.2.op.txid

-- `mint_end` reports the expired lock
#guard end2.2.2 == .error (.mintLockExpired (toString m2.2.2.opid) 65)
-- and fails the mint, releasing its inputs
#guard statusOf end2.1 mint2Idx == some .failed && end2.1.db.reservedColored.isEmpty
-- its mint right can be spent again
#guard rights end2.1 == 2
def bobX2 : Refreshed := refreshed bobX1.1 wExp bobMO
-- the receiver refuses the checked mint whose lock expired
#guard reported bobX2 rcv2.2.2.batchTransferIdx == some ⟨some .failed, none⟩
-- nothing is left to lock for it
#guard bobX2.1.getReceivedMint rcv2.2.2.recipientId == []
-- both paths are of the status machine
#guard validPath false [.initiated, .failed] && validPath true [.waitingCounterparty, .failed]

/-! ## `fail_transfers` on a pending mint -/

def rcv3 : Wallet × World × ReceiveData := bobInvoice bobX2.1 end2.2.1 500
def m3 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy end2.1 rcv3.2.1 (toMint rcv3.2.2 500) 75).toOption.get!
def mint3Idx : Nat := m3.2.2.batchTransferIdx
def failNow : Wallet × World × Result Bool :=
  m3.1.failTransfers m3.2.1 aliceMO (some mint3Idx)

-- a mint whose lock may still be included cannot be failed
#guard failNow.2.2 == .error .cannotFailBatchTransfer &&
  statusOf failNow.1 mint3Idx == some .initiated
-- nor without an index: a mint does not expire by a timestamp
#guard (m3.1.failTransfers (m3.2.1.setTime (m3.2.1.now + 400000000)) aliceMO).2.2
  == .ok false

/-- Block 74 is finalized without the lock of the mint committing to block 75. -/
def wExp3 : World := withLedger m3.2.1 (ledgerAt 79 74 [⟨lockM, 500, 52⟩] 500)
def failed3 : Wallet × World × Result Bool :=
  m3.1.failTransfers wExp3 aliceMO (some mint3Idx)

-- once its lock expired it fails
#guard failed3.2.2 == .ok true && statusOf failed3.1 mint3Idx == some .failed
-- without an index too
#guard (m3.1.failTransfers wExp3 aliceMO).2.2 == .ok true
-- not when only transfers without an asset may fail
#guard (m3.1.failTransfers wExp3 aliceMO (some mint3Idx) (noAssetOnly := true)).2.2
  == .error .cannotFailBatchTransfer
/-- Alice online without EVM chains: the lock of a sent mint cannot be checked. -/
def aliceNoEvm : Wallet × Online × Result Unit := m3.1.goOnline wExp3
-- without an index the mint is skipped, with one the error is reported
#guard (aliceNoEvm.1.failTransfers wExp3 aliceNoEvm.2.1).2.2 == .ok false &&
  (aliceNoEvm.1.failTransfers wExp3 aliceNoEvm.2.1 (some mint3Idx)).2.2 == .error (.noEvmRpcUrl 1)

/-! ## Mints a receiver refuses -/

def rcv4 : Wallet × World × ReceiveData := bobInvoice bobM wm0 400
def m4 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy aliceM rcv4.2.1 (toMint rcv4.2.2 500) 80).toOption.get!
def bobY : Refreshed := refreshed rcv4.1 m4.2.1 bobMO

-- the claim locks 500 while the invoice asks for 400: refused
#guard reported bobY rcv4.2.2.batchTransferIdx == some ⟨some .failed, none⟩
-- before it is checked: nothing to lock for it
#guard bobY.1.getReceivedMint rcv4.2.2.recipientId == []
-- a wallet that does not accept mints refuses one (a multisig wallet)
#guard reported (refreshed { bobR1 with acceptsReceivedMints := false } wm2 bobMO)
    inv.batchTransferIdx == some ⟨some .failed, none⟩
def bobNoEvm : Wallet := (bob1.goOnline wm0).1
def rcv5 : Wallet × World × ReceiveData :=
  (bobNoEvm.blindReceive wm0 none (.fungible 500) (wm0.now + 86400) [endpoint]
    (online := some ⟨wm0.now⟩)).toOption.get!
def m5 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy aliceM rcv5.2.1 (toMint rcv5.2.2 500) 80).toOption.get!
def bobZ : Refreshed := refreshed rcv5.1 m5.2.1 ⟨wm0.now⟩
-- without an RPC URL for the bridge's chain the receiver waits, without checking the mint
#guard reported bobZ rcv5.2.2.batchTransferIdx == some ⟨none, none⟩ &&
  bobZ.1.getReceivedMint rcv5.2.2.recipientId == []

/-- Bob with locks at most 20 blocks after the latest block. -/
def bobNear : Wallet := (bob1.goOnline wm0 (evmChains := [(1, ⟨evmUrl, 5, 20⟩)])).1
def rcv6 : Wallet × World × ReceiveData :=
  (bobNear.blindReceive wm0 none (.fungible 500) (wm0.now + 86400) [endpoint]
    (online := some ⟨wm0.now⟩)).toOption.get!
def m6 : Wallet × World × Wallet.MintBeginResult :=
  (mintBy aliceM rcv6.2.1 (toMint rcv6.2.2 500) 80).toOption.get!
-- a mint committing to a block too far after the latest one, its lock not recorded: refused
#guard reported (refreshed rcv6.1 m6.2.1 ⟨wm0.now⟩) rcv6.2.2.batchTransferIdx
  == some ⟨some .failed, none⟩
/-- The lock of that mint recorded at block 52, not finalized. -/
def wRec6 : World :=
  withLedger m6.2.1 (ledgerAt 55 50 [⟨LockId.of m6.2.2.opid m6.2.2.op.txid, 500, 52⟩] 500)
def bobRec6 : Refreshed := refreshed rcv6.1 wRec6 ⟨wm0.now⟩
-- with its lock recorded the bound does not apply: the mint is checked and waits
#guard reported bobRec6 rcv6.2.2.batchTransferIdx == some ⟨none, none⟩ &&
  (bobRec6.1.getReceivedMint rcv6.2.2.recipientId).length == 1
def rcvD : Wallet × World × ReceiveData := bobInvoice bobM wm0 500
/-- A mint whose sender proxy does not answer. -/
def mD : Wallet × World × Wallet.MintBeginResult :=
  (aliceM.mintBegin rcvD.2.1 aliceMO bfa (toMint rcvD.2.2 500) 60 1 1
    "rpc://down.test/json-rpc").toOption.get!
-- refused once its lock expired, it is not NACKed: nothing reaches the sender proxy
#guard reported (refreshed rcvD.1 (withLedger mD.2.1 (ledgerAt 70 65)) bobMO)
  rcvD.2.2.batchTransferIdx == some ⟨some .failed, none⟩

/-! ## Mints to invoices asking for no amount -/

/-- Bob's check of a mint of 500 to his receive of `a`. -/
def mintedTo (a : Assignment) : Option RefreshedTransfer × List Nat :=
  let r := (bobM.blindReceive wm0 none a (wm0.now + 86400) [endpoint]
    (online := some bobMO)).toOption.get!
  let m := (mintBy aliceM r.2.1 (toMint r.2.2 500) 80).toOption.get!
  let b := refreshed r.1 m.2.1 bobMO
  (reported b r.2.2.batchTransferIdx, (b.1.getReceivedMint r.2.2.recipientId).map (·.amount))
-- an invoice asking for no amount, or for any, takes a mint of any amount: it is checked
#guard mintedTo (.fungible 0) == (some ⟨none, none⟩, [500]) &&
  mintedTo .any == (some ⟨none, none⟩, [500])

/-! ## A checked mint whose inputs are spent elsewhere -/

/-- The mint right's UTXO spent by another transaction, mined, before the mint is broadcast. -/
def spentElsewhere : World :=
  let tx := mkTx (mintOp.tx.inputs.map (·.prevout)) [⟨500, .p2wpkh "elsewhere"⟩]
  { bobC3.2.1 with chain := ((bobC3.2.1.chain.broadcast tx).toOption.getD bobC3.2.1.chain).mine }

-- the receiver waiting for the broadcast fails the mint: its transaction can never confirm
#guard reported (refreshed bobC3.1 spentElsewhere bobMO) inv.batchTransferIdx
  == some ⟨some .failed, none⟩
-- a path of the status machine
#guard validPath true [.waitingCounterparty, .waitingBroadcast, .failed]


/-! ## Mint rights moved by a send -/

/-- Five mint rights, one on each UTXO, then NIA 600 and 400 on two of them. -/
def everyUtxo : Wallet × DbAsset :=
  ((alice3.issueAssetBfa 1700000600 "₿" "Bridged" 0 5 1 bridgeHex).toOption.get!.1.issueAssetNia
    1700000700 "USDX" "Tether" 2 [600, 400]).toOption.get!
def everyOn : Wallet × Online × Result Unit := everyUtxo.1.goOnline world2
/-- A send of `n` of the NIA asset. -/
def sendNia (n : UInt64) : Result Txid :=
  let r : Recipient := { toBob with assignment := .fungible n }
  (everyOn.1.sendBegin world2 everyOn.2.1 [(everyUtxo.2.id, [r])] false 1 1
    (world2.now + 3600)).map (·.2.txid)
-- a send of 400 spends one of them: its mint right moves to the bitcoin change
#guard sendNia 400 matches .ok _
-- one of 700 spends both: the second right finds no destination holding none of the asset's
#guard sendNia 700 == .error .insufficientAllocationSlots
end Rgb.Examples.MintScenario
