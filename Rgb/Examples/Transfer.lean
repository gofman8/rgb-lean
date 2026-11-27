import Rgb.Lib.Refresh
import Rgb.Lib.StateMachine
import Rgb.Examples.Wallet

/-!
# Transfer scenarios

Alice issues 1000 USDT and sends 600 to Bob with the out-of-band exchange: Bob
creates a blind receive, Alice prepares and signs the transfer, Bob checks the
consignment and ACKs, Alice broadcasts, a block confirms it, and both refresh to
settled. Then a donation, a witness receive and the failure paths.
-/

namespace Rgb.Examples.TransferScenario

open Rgb Rgb.Lib Rgb.Examples.WalletScenario

/-- Bob: a wallet with five colored UTXOs on the same chain. -/
def bob0 : Wallet := (Wallet.create dataOf (keysOf "bob")).toOption.get!
def bobFund : Script × Wallet := bob0.getAddress
def worldB : World := { world1 with chain := (world1.chain.fund bobFund.1 50000 9).1 }
def bobOnline : Wallet × Online × Result Unit := bobFund.2.goOnline worldB
def bobO : Online := bobOnline.2.1
def bobCreated : Wallet × World × Nat := (bobOnline.1.createUtxos worldB bobO false).toOption.get!
def bob1 : Wallet := bobCreated.1
def world2 : World := { bobCreated.2.1 with chain := bobCreated.2.1.chain.mine, now := 1700001000 }

/-- Alice goes online in the same world with her issued USDT. -/
def aliceOn : Wallet × Online × Result Unit := alice4.goOnline world2
def alice5 : Wallet := aliceOn.1
def aliceO : Online := aliceOn.2.1

#guard aliceOn.2.2 == .ok ()
#guard alice5.assetBalance usdt == ⟨1000, 1000, 1000⟩

/-! ## Blind receive and send, out of band -/

/-- The wallet and receive data of a receive that must succeed (out of band: the world stays). -/
def received (r : Result (Wallet × World × ReceiveData)) : Wallet × ReceiveData :=
  let (w, _, d) := r.toOption.get!
  (w, d)

def recv : Wallet × ReceiveData :=
  received (bob1.blindReceive world2 none (.fungible 600) (world2.now + 86400))
def bob2 : Wallet := recv.1
def invoice : ReceiveData := recv.2

def statusOf (w : Wallet) (i : Nat) : Option TransferStatus := (w.db.batch? i).map (·.status)

-- Bob does not know the asset yet: a receive naming it is refused
#guard (bob1.blindReceive world2 (some usdt) (.fungible 600) (world2.now + 86400)).map
    (·.2.2.invoice)
  == .error (.assetNotFound usdt)
-- the receive waits for its counterparty and reserves a slot on a Bob UTXO
#guard statusOf bob2 invoice.batchTransferIdx == some .waitingCounterparty
#guard (bob2.listUnspents.filter (·.pendingBlinded == 1)).length == 1

def toBob : Recipient := { recipientId := invoice.recipientId, assignment := .fungible 600 }

def begun : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO [(usdt, [toBob])] false 1 1 (world2.now + 3600)).toOption.get!
def ended : Wallet × World × List (String × Consignment) :=
  (begun.1.sendEnd world2 aliceO begun.2.txid).toOption.get!
def alice6 : Wallet := ended.1
def consignment : Consignment := (ended.2.2.headD default).2

-- Alice waits for Bob's ACK; her 600 are pending out, the 400 change pending in
#guard alice6.transferStatuses usdt |>.map (·.2.1) |>.contains .waitingCounterparty
#guard alice6.assetBalance usdt == ⟨1000, 400, 0⟩
-- the consignment carries genesis and the transfer bundle
#guard consignment.bundles.length == 1 && consignment.genesis.contractId.d.data != ""

/-- Bob checks the consignment and ACKs (out of band). -/
def bobGot : Wallet × World × List (Nat × RefreshedTransfer) :=
  (bob2.provideOutOfBandConsignment world2 bobO consignment).toOption.get!
def bob3 : Wallet := bobGot.1

#guard bobGot.2.2 == [(invoice.batchTransferIdx, ⟨some .waitingBroadcast, none⟩)]
#guard bob3.assetBalance usdt == ⟨0, 600, 0⟩

/-- Alice receives the ACK and broadcasts. -/
def acked : Wallet × World × Option Txid := (alice6.provideOutOfBandAck world2 aliceO invoice.recipientId).toOption.get!
def alice7 : Wallet := acked.1
def world3 : World := { acked.2.1 with chain := acked.2.1.chain.mine, now := world2.now + 600 }

#guard acked.2.2 == some begun.2.txid
#guard (world3.chain.confirmations begun.2.txid) == 1

/-- Both refresh: one confirmation is enough. -/
def bobDone : Wallet × World × List (Nat × RefreshedTransfer) := (bob3.refresh world3 bobO).toOption.get!
def aliceDone : Wallet × World × List (Nat × RefreshedTransfer) := (alice7.refresh world3 aliceO).toOption.get!

#guard bobDone.1.transferStatuses usdt == [(invoice.batchTransferIdx, .settled, .receiveBlind)]
#guard bobDone.1.assetBalance usdt == ⟨600, 600, 600⟩
#guard aliceDone.1.assetBalance usdt == ⟨400, 400, 400⟩
-- Bob's stash knows every revealed allocation of the history (Alice's issuance of
-- 600 + 400, her change of 400, his 600); what Bob owns is what sits on his UTXOs
#guard ((bobDone.1.stock.allocations consignment.contractId).map (·.2.2)).length == 4
#guard ((bobDone.1.stock.allocations consignment.contractId).filter fun (o, _, _) =>
  bobDone.1.db.txos.any (·.outpoint == o)).map (·.2.2) == [.amount 600]

/-! ## Rules of send -/

-- more than the wallet holds
#guard (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with assignment := .fungible 2000 }])] false 1 1
    (world2.now + 3600)).map (·.2.txid) == .error (.insufficientAssignments usdt 1000)
-- a zero amount, an empty recipient map, an operation expiring too soon
#guard (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with assignment := .fungible 0 }])] false 1 1
    (world2.now + 3600)).map (·.2.txid) == .error .invalidAmountZero
#guard (alice5.sendBegin world2 aliceO [] false 1 1 (world2.now + 3600)).map (·.2.txid) == .error .invalidRecipientMap
#guard (alice5.sendBegin world2 aliceO [(usdt, [toBob])] false 1 1 (world2.now + 60)).map (·.2.txid)
  == .error .invalidExpiration
-- the same recipient twice
#guard (alice5.sendBegin world2 aliceO [(usdt, [toBob, toBob])] false 1 1 (world2.now + 3600)).map (·.2.txid)
  == .error .recipientIdDuplicated
-- a recipient of another network
#guard (alice5.sendBegin world2 aliceO
    [(usdt, [{ toBob with recipientId := "bc" ++ (invoice.recipientId.drop 4).toString }])] false 1 1
    (world2.now + 3600)).map (·.2.txid) == .error .invalidRecipientNetwork
-- an assignment the schema does not support
#guard (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with assignment := .nonFungible }])] false 1 1
    (world2.now + 3600)).map (·.2.txid) == .error .invalidAssignment
-- an out-of-band ACK for an unknown recipient
#guard (alice6.provideOutOfBandAck world2 aliceO "bcrt:utxob:x|y").map (·.2.2)
  == .error (.cannotProvideOutOfBandAck "no transfer found for the provided recipient ID")
-- one after the operation expired cannot complete the unreleased send
#guard (alice6.provideOutOfBandAck (world2.setTime (world2.now + 3601)) aliceO
    invoice.recipientId).map (·.2.2)
  == .error (.cannotProvideOutOfBandAck "transfer could not be completed")
-- a begun send is an operation a backup misses, a dry run is not
#guard begun.1.db.backupInfo.lastOperationTimestamp == world2.now &&
  (alice5.sendBegin world2 aliceO [(usdt, [toBob])] false 1 1 (world2.now + 3600)
    (dryRun := true)).map (·.1.db.backupInfo.lastOperationTimestamp)
    == .ok alice5.db.backupInfo.lastOperationTimestamp

/-! ## Donation -/

def donRecv : Wallet × ReceiveData :=
  received (bob1.blindReceive world2 none (.fungible 100) (world2.now + 86400))
def donBegun : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with recipientId := donRecv.2.recipientId, assignment := .fungible 100 }])]
    true 1 1 (world2.now + 3600)).toOption.get!
def donEnded : Wallet × World × List (String × Consignment) := (donBegun.1.sendEnd world2 aliceO donBegun.2.txid).toOption.get!

-- a donation is broadcast at once and waits for confirmations
#guard donEnded.1.transferStatuses usdt |>.map (·.2.1) |>.contains .waitingConfirmations
#guard (donEnded.2.1.chain.witnessOrd donBegun.2.txid) == .tentative
-- the receiver sees the witness already on chain: no ACK round
#guard ((donRecv.1.provideOutOfBandConsignment donEnded.2.1 bobO (donEnded.2.2.headD default).2).map (·.2.2))
  == .ok [(donRecv.2.batchTransferIdx, ⟨some .waitingConfirmations, none⟩)]

/-! ## Witness receive -/

def witRecv : Wallet × ReceiveData :=
  received (bob1.witnessReceive world2 none (.fungible 50) (world2.now + 86400))
def witBegun : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO
    [(usdt, [{ recipientId := witRecv.2.recipientId, assignment := .fungible 50, witnessData := some ⟨1000, none⟩ }])]
    true 1 1 (world2.now + 3600)).toOption.get!
def witEnded : Wallet × World × List (String × Consignment) := (witBegun.1.sendEnd world2 aliceO witBegun.2.txid).toOption.get!
def bobWit : Wallet × World × List (Nat × RefreshedTransfer) :=
  (witRecv.1.provideOutOfBandConsignment witEnded.2.1 bobO (witEnded.2.2.headD default).2).toOption.get!

-- the witness transaction pays Bob's address at output 1 (output 0 is the commitment)
#guard (witBegun.2.tx.outputs.map (·.value)).take 2 == [0, 1000]
-- Bob registers the new output as pending until it settles
#guard bobWit.2.2 == [(witRecv.2.batchTransferIdx, ⟨some .waitingConfirmations, none⟩)]
#guard (bobWit.1.db.txos.filter (·.pendingWitness)).length == 1
def witWorld : World := { bobWit.2.1 with chain := bobWit.2.1.chain.mine }
def bobWitDone : Wallet × World × List (Nat × RefreshedTransfer) := (bobWit.1.refresh witWorld bobO).toOption.get!
#guard bobWitDone.1.assetBalance usdt == ⟨50, 50, 50⟩
#guard (bobWitDone.1.db.txos.filter (·.pendingWitness)).length == 0
/-- Two witness receives of Bob paid by one transaction, the first expiring sooner. -/
def twoA : Wallet × ReceiveData :=
  received (bob1.witnessReceive world2 none (.fungible 50) (world2.now + 4000))
def twoB : Wallet × ReceiveData :=
  received (twoA.1.witnessReceive world2 none (.fungible 30) (world2.now + 86400))
def twoBegun : Wallet × PendingOp :=
  let to (d : ReceiveData) (n : UInt64) : Recipient :=
    { recipientId := d.recipientId, assignment := .fungible n
      witnessData := some ⟨1000, none⟩ }
  (alice5.sendBegin world2 aliceO [(usdt, [to twoA.2 50, to twoB.2 30])] false 1 1
    (world2.now + 3600)).toOption.get!
def twoEnded : Wallet × World × List (String × Consignment) :=
  (twoBegun.1.sendEnd world2 aliceO twoBegun.2.txid).toOption.get!
def twoGot : Wallet × World × List (Nat × RefreshedTransfer) :=
  let c := (twoEnded.2.2.headD default).2
  (twoB.1.provideOutOfBandConsignment twoEnded.2.1 bobO c).toOption.get!
/-- The outputs of the transaction that wait for their receive. -/
def waitingOuts (w : Wallet) : List UInt32 :=
  (w.db.txos.filter fun t => t.outpoint.txid == twoBegun.2.txid && t.pendingWitness).map
    (·.outpoint.vout)
-- both outputs wait for their receives
#guard waitingOuts twoGot.1 == [1, 2]
-- the first receive, failed once expired, frees its output only
#guard waitingOuts (twoGot.1.failTransfers (world2.setTime (world2.now + 50000)) bobO
  (some twoA.2.batchTransferIdx)).1 == [2]

/-! ## Failing and deleting -/

-- a pending receive cannot be deleted; once expired it can be failed, then deleted
#guard (bob2.deleteTransfers world2.now (some invoice.batchTransferIdx)).map (·.2) == .error .cannotDeleteBatchTransfer
def late : World := { world2 with now := world2.now + 86400 + 1 }
def bobFailed : Wallet × World × Result Bool := bob2.failTransfers late bobO
#guard bobFailed.2.2 == .ok true && statusOf bobFailed.1 invoice.batchTransferIdx == some .failed
-- the reserved slot is free again
#guard (bobFailed.1.listUnspents.filter (·.pendingBlinded == 1)).length == 0
#guard ((bobFailed.1.deleteTransfers late.now (some invoice.batchTransferIdx)).map fun (w, d) =>
  (d, statusOf w invoice.batchTransferIdx)) == .ok (true, none)
-- a settled transfer cannot be failed
#guard (bobDone.1.failTransfers world3 bobO (some invoice.batchTransferIdx)).2.2
  == .error .cannotFailBatchTransfer
/-- A send of all of the asset: no RGB change, its bitcoin change registered before broadcast. -/
def sendAll : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with assignment := .fungible 1000 }])] false 1 1
    (world2.now + 3600)).toOption.get!
def sendAllIdx : Nat := ((sendAll.1.db.batchByTxid? sendAll.2.txid false).map (·.idx)).getD 0
def sendAllFailed : Wallet × World × Result Bool :=
  sendAll.1.failTransfers world2 aliceO (some sendAllIdx)
/-- Whether a wallet keeps a row of an output of that send's transaction. -/
def keepsSendAllOut (w : Wallet) : Bool := w.db.txos.any (·.outpoint.txid == sendAll.2.txid)
-- failed, it keeps the change output's row; deleted, the row goes with it
#guard sendAllFailed.2.2 == .ok true && keepsSendAllOut sendAllFailed.1 &&
  (sendAllFailed.1.deleteTransfers world2.now (some sendAllIdx)).map (keepsSendAllOut ·.1)
    == .ok false

/-! ## The paths taken are allowed by the status machine -/

-- Bob's blind receive: created, ACKed out of band, settled
#guard validPath true [.waitingCounterparty, .waitingBroadcast, .settled]
-- Alice's send: initiated by begin, waiting for the ACK, broadcast, settled
#guard validPath false [.initiated, .waitingCounterparty, .waitingConfirmations, .settled]
-- the donation and the witness receive
#guard validPath false [.initiated, .waitingConfirmations, .settled]
#guard validPath true [.waitingCounterparty, .waitingConfirmations, .settled]
-- the expired receive failed by `fail_transfers`
#guard validPath true [.waitingCounterparty, .failed]
-- and paths rgb-lib never takes
#guard !validPath true [.waitingCounterparty, .settled]
#guard !validPath false [.settled, .failed]
#guard !validPath true [.initiated]

end Rgb.Examples.TransferScenario
