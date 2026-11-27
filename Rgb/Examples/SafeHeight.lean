import Rgb.Examples.Transfer

/-!
# Safe height, listings and the consistency check

Carol accepts payments with zero confirmations, so she can spend an asset whose
transfer is still in the mempool. When she pays Bob, who asks for one
confirmation, Bob's validation finds unconfirmed history: his receive waits in
`waitingSafeHeight` until that history is mined.
-/

namespace Rgb.Examples.SafeHeightScenario

open Rgb Rgb.Lib Rgb.Examples.WalletScenario Rgb.Examples.TransferScenario

/-- Carol: funded, online, five colored UTXOs. -/
def carol0 : Wallet := (Wallet.create dataOf (keysOf "carol")).toOption.get!
def carolFund : Script × Wallet := carol0.getAddress
def wC : World := { world2 with chain := (world2.chain.fund carolFund.1 50000 21).1 }
def carolOn : Wallet × Online × Result Unit := carolFund.2.goOnline wC
def carolO : Online := carolOn.2.1
def carolUtxos : Wallet × World × Nat := (carolOn.1.createUtxos wC carolO false).toOption.get!
def wC1 : World := { carolUtxos.2.1 with chain := carolUtxos.2.1.chain.mine }

/-- Alice donates 300 to Carol, who settles with zero confirmations. -/
def carolRecv : Wallet × ReceiveData :=
  (carolUtxos.1.blindReceive wC1.now none (.fungible 300) (wC1.now + 86400) (minConfirmations := 0)).toOption.get!
def aliceOnC : Wallet × Online × Result Unit := alice5.goOnline wC1
def toCarol : Wallet × PendingOp :=
  (aliceOnC.1.sendBegin wC1 aliceOnC.2.1 [(usdt, [{ recipientId := carolRecv.2.recipientId, assignment := .fungible 300 }])]
    true 1 1 (wC1.now + 3600)).toOption.get!
def toCarolEnd : Wallet × World × List (String × Consignment) :=
  (toCarol.1.sendEnd wC1 aliceOnC.2.1 toCarol.2.txid).toOption.get!
def wC2 : World := toCarolEnd.2.1
def carolGot : Wallet × World × List (Nat × TransferStatus) :=
  (carolRecv.1.provideOutOfBandConsignment wC2 carolO (toCarolEnd.2.2.headD default).2).toOption.get!
def carolSettled : Wallet := (carolGot.1.refresh wC2 carolO).toOption.get!.1

-- with zero confirmations a transaction in the mempool settles
#guard wC2.chain.confirmations toCarol.2.txid == 0
#guard carolSettled.assetBalance usdt == ⟨300, 300, 300⟩

/-- Carol pays 100 to Bob, who asks for one confirmation. -/
def bobRecv : Wallet × ReceiveData :=
  (bob1.blindReceive wC2.now none (.fungible 100) (wC2.now + 86400) (minConfirmations := 1)).toOption.get!
def toBob : Wallet × PendingOp :=
  (carolSettled.sendBegin wC2 carolO [(usdt, [{ recipientId := bobRecv.2.recipientId, assignment := .fungible 100 }])]
    true 1 1 (wC2.now + 3600)).toOption.get!
def toBobEnd : Wallet × World × List (String × Consignment) :=
  (toBob.1.sendEnd wC2 carolO toBob.2.txid).toOption.get!
def wC3 : World := toBobEnd.2.1
def bobGot : Wallet × World × List (Nat × TransferStatus) :=
  (bobRecv.1.provideOutOfBandConsignment wC3 bobO (toBobEnd.2.2.headD default).2).toOption.get!

-- the consignment carries Alice's unconfirmed transfer to Carol: unsafe history
#guard (toBobEnd.2.2.headD default).2.bundles.length == 2
#guard bobGot.2.2 == [(bobRecv.2.batchTransferIdx, .waitingSafeHeight)]
-- refresh changes nothing while the history is unconfirmed
#guard ((bobGot.1.refresh wC3 bobO).toOption.get!.2.2.find? (·.1 == bobRecv.2.batchTransferIdx)).map (·.2.updatedStatus)
  == some none
-- one block confirms both transactions: the history is safe, the payment confirmed
def wC4 : World := { wC3 with chain := wC3.chain.mine }
def bobSafe : Wallet := (bobGot.1.refresh wC4 bobO).toOption.get!.1
def bobDone : Wallet := (bobSafe.refresh wC4 bobO).toOption.get!.1
#guard (bobSafe.db.batch? bobRecv.2.batchTransferIdx).map (·.status) == some .waitingConfirmations
#guard (bobDone.db.batch? bobRecv.2.batchTransferIdx).map (·.status) == some .settled
#guard bobDone.assetBalance usdt == ⟨100, 100, 100⟩
-- the path is one rgb-lib takes
#guard validPath true [.waitingCounterparty, .waitingSafeHeight, .waitingConfirmations, .settled]

/-! ## Listings -/

-- Bob lists one NIA asset, with its balance
#guard (bobDone.listAssets).map (fun a => (a.schema, a.balance)) == [(.nia, ⟨100, 100, 100⟩)]
#guard (bobDone.listAssets [.uda]).isEmpty
-- Carol's transfers of the asset: received 300 (settled), sent 100 (waiting confirmations)
#guard ((carolSettled.listTransfers (some usdt)).map fun l => l.map (·.kind)) == .ok [.receiveBlind]
#guard ((toBobEnd.1.listTransfers (some usdt)).map fun l => l.map (fun t => (t.kind, t.status)))
  == .ok [(.receiveBlind, .settled), (.send, .waitingConfirmations)]
#guard (bob1.listTransfers (some "rgb:none")) matches .error (.assetNotFound _)

/-! ## The consistency check -/

-- Carol's UTXOs spent by another wallet with her keys: going online reports it
def carolNow : Wallet := toBobEnd.1
def stolen : Outpoint := (carolNow.db.txos.find? fun t => !t.spent && t.exists_ && wC4.chain.isUnspent t.outpoint).get!.outpoint
def wThief : World := { wC4 with chain := ((wC4.chain.broadcast (mkTx [stolen] [⟨500, .p2wpkh "thief"⟩])).toOption.get!) }
#guard (carolNow.goOnline wThief).2.2 matches .error (.inconsistency _)
#guard (carolNow.goOnline wC4).2.2 == .ok ()

end Rgb.Examples.SafeHeightScenario
