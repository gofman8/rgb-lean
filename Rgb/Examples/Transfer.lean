import Rgb.Lib.Refresh
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

def recv : Wallet × ReceiveData := (bob1.blindReceive world2.now none (.fungible 600) (world2.now + 86400)).toOption.get!
def bob2 : Wallet := recv.1
def invoice : ReceiveData := recv.2

def statusOf (w : Wallet) (i : Nat) : Option TransferStatus := (w.db.batch? i).map (·.status)

-- Bob does not know the asset yet: a receive naming it is refused
#guard (bob1.blindReceive world2.now (some usdt) (.fungible 600) (world2.now + 86400)).map (·.2.invoice)
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
def bobGot : Wallet × World × List (Nat × TransferStatus) :=
  (bob2.provideOutOfBandConsignment world2 bobO consignment).toOption.get!
def bob3 : Wallet := bobGot.1

#guard bobGot.2.2 == [(invoice.batchTransferIdx, .waitingBroadcast)]
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

/-! ## Donation -/

def donRecv : Wallet × ReceiveData := (bob1.blindReceive world2.now none (.fungible 100) (world2.now + 86400)).toOption.get!
def donBegun : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO [(usdt, [{ toBob with recipientId := donRecv.2.recipientId, assignment := .fungible 100 }])]
    true 1 1 (world2.now + 3600)).toOption.get!
def donEnded : Wallet × World × List (String × Consignment) := (donBegun.1.sendEnd world2 aliceO donBegun.2.txid).toOption.get!

-- a donation is broadcast at once and waits for confirmations
#guard donEnded.1.transferStatuses usdt |>.map (·.2.1) |>.contains .waitingConfirmations
#guard (donEnded.2.1.chain.witnessOrd donBegun.2.txid) == .tentative
-- the receiver sees the witness already on chain: no ACK round
#guard ((donRecv.1.provideOutOfBandConsignment donEnded.2.1 bobO (donEnded.2.2.headD default).2).map (·.2.2))
  == .ok [(donRecv.2.batchTransferIdx, .waitingConfirmations)]

/-! ## Witness receive -/

def witRecv : Wallet × ReceiveData := (bob1.witnessReceive world2.now none (.fungible 50) (world2.now + 86400)).toOption.get!
def witBegun : Wallet × PendingOp :=
  (alice5.sendBegin world2 aliceO
    [(usdt, [{ recipientId := witRecv.2.recipientId, assignment := .fungible 50, witnessData := some ⟨1000, none⟩ }])]
    true 1 1 (world2.now + 3600)).toOption.get!
def witEnded : Wallet × World × List (String × Consignment) := (witBegun.1.sendEnd world2 aliceO witBegun.2.txid).toOption.get!
def bobWit : Wallet × World × List (Nat × TransferStatus) :=
  (witRecv.1.provideOutOfBandConsignment witEnded.2.1 bobO (witEnded.2.2.headD default).2).toOption.get!

-- the witness transaction pays Bob's address at output 1 (output 0 is the commitment)
#guard (witBegun.2.tx.outputs.map (·.value)).take 2 == [0, 1000]
-- Bob registers the new output as pending until it settles
#guard bobWit.2.2 == [(witRecv.2.batchTransferIdx, .waitingConfirmations)]
#guard (bobWit.1.db.txos.filter (·.pendingWitness)).length == 1
def witWorld : World := { bobWit.2.1 with chain := bobWit.2.1.chain.mine }
def bobWitDone : Wallet × World × List (Nat × RefreshedTransfer) := (bobWit.1.refresh witWorld bobO).toOption.get!
#guard bobWitDone.1.assetBalance usdt == ⟨50, 50, 50⟩
#guard (bobWitDone.1.db.txos.filter (·.pendingWitness)).length == 0

/-! ## Failing and deleting -/

-- a pending receive cannot be deleted; once expired it can be failed, then deleted
#guard (bob2.deleteTransfers world2.now (some invoice.batchTransferIdx)).map (·.2) == .error .cannotDeleteBatchTransfer
def late : World := { world2 with now := world2.now + 86400 + 1 }
def bobFailed : Wallet × Bool := (bob2.failTransfers late bobO).toOption.get!
#guard bobFailed.2 && statusOf bobFailed.1 invoice.batchTransferIdx == some .failed
-- the reserved slot is free again
#guard (bobFailed.1.listUnspents.filter (·.pendingBlinded == 1)).length == 0
#guard ((bobFailed.1.deleteTransfers late.now (some invoice.batchTransferIdx)).map fun (w, d) =>
  (d, statusOf w invoice.batchTransferIdx)) == .ok (true, none)
-- a settled transfer cannot be failed
#guard (bobDone.1.failTransfers world3 bobO (some invoice.batchTransferIdx)).map (·.2) == .error .cannotFailBatchTransfer

end Rgb.Examples.TransferScenario
