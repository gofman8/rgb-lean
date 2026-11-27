import Rgb.Lib.Contracts
import Rgb.Lib.Operations
import Rgb.Examples.Transfer

/-!
# Contract import and export, fee estimation

Then an IFA asset imported or received: what its row shows, and its known circulating supply as
transfers with inflations in their history arrive.
-/

namespace Rgb.Examples.ContractsScenario

open Rgb Rgb.Lib Rgb.Examples.WalletScenario Rgb.Examples.TransferScenario

def exported : Consignment := (alice5.exportContract usdt).toOption.get!

-- the exported contract is genesis only
#guard !exported.transfer && exported.bundles.isEmpty
-- Bob imports it: the asset is known, with no balance
def bobImported : Wallet := (bob1.importContract world2.now exported).toOption.get!
#guard (bobImported.listAssets).map (fun a => (a.assetId, a.balance)) == [(usdt, ⟨0, 0, 0⟩)]
-- importing twice, a transfer consignment, an unknown asset to export
#guard (bobImported.importContract world2.now exported) matches .error (.assetAlreadyKnown _)
#guard (bob1.importContract world2.now { exported with transfer := true }) matches .error (.invalidContract _)
#guard (bob1.exportContract "rgb:none") matches .error (.assetNotFound _)
-- a contract of another network is refused by validation
def mainnetWallet : Wallet :=
  (Wallet.create { dataOf [.nia] with bitcoinNetwork := .mainnet } (keysOf "m" .mainnet))
    |>.toOption.get!
#guard (mainnetWallet.importContract world2.now exported) matches .error (.consignmentValidationFailed _)
-- a contract larger than 16 MiB is refused before reading it
#guard (bob1.importContract world2.now exported (size := 16 * 1024 * 1024 + 1)) matches .error (.fileTooLarge _ _)

-- fee estimation: exact targets, interpolation, bounds
def estimates : List (Nat × Nat) := [(1, 20), (6, 10), (144, 2)]
#guard Wallet.feeEstimation estimates 6 == .ok 10
#guard Wallet.feeEstimation estimates 3 == .ok 16
#guard Wallet.feeEstimation estimates 0 == .error .invalidEstimationBlocks
#guard Wallet.feeEstimation estimates 1009 == .error .invalidEstimationBlocks
#guard Wallet.feeEstimation [] 6 == .error .cannotEstimateFees
#guard Wallet.feeEstimation estimates 500 == .error (.internal "esplora map doesn't contain the expected keys")


/-! ## An IFA asset imported or received -/

/-- Alice's IFA asset: 100 issued, 50 more allowed, a reject list. -/
def ifaIssued : Wallet × DbAsset :=
  (alice5.issueAssetIfa world2.now "INF" "Inflatable" 0 [100] [50]
    (rejectListUrl := some "https://rl.test")).toOption.get!
def ifaId : String := ifaIssued.2.id
def inflatedIfa : Wallet × World × Txid :=
  (ifaIssued.1.inflate world2 aliceO ifaId [30]).toOption.get!
def wInf : World := { inflatedIfa.2.1 with chain := inflatedIfa.2.1.chain.mine }
/-- Alice after the inflation of 30 settled, then issuing an asset linked from hers. -/
def aliceInf : Wallet × DbAsset :=
  ((inflatedIfa.1.refresh wInf aliceO).toOption.get!.1.issueAssetIfa wInf.now "KID" "Child" 0 [5] []
    (linkedFrom := some ifaId)).toOption.get!
/-- The genesis-only consignment of an asset of Alice's. -/
def contractOf (id : String) : Consignment := (aliceInf.1.exportContract id).toOption.get!
def bobIfa : Wallet :=
  ((bob1.importContract world2.now (contractOf ifaId)).toOption.get!.importContract world2.now
    (contractOf aliceInf.2.id)).toOption.get!
-- imported, the asset shows its max supply, its initial supply as circulating, its reject list
#guard ((bobIfa.listAssets [.ifa]).map fun a =>
    (a.maxSupply, a.knownCirculatingSupply, a.rejectList))
  == [(150, 100, some (.url ⟨"https://rl.test"⟩)), (5, 5, none)]
-- the linked one shows the contract it was issued linked from
#guard (bobIfa.db.asset? aliceInf.2.id).bind (·.linkedFromContract) == some ifaId
/-- `w`'s receive of the 130 Alice holds, sent and handed over out of band: the receiver's wallet,
the world, the receive and the sender's wallet. -/
def got130 (w : Wallet) : Wallet × World × ReceiveData × Wallet :=
  let r := received (w.blindReceive wInf none (.fungible 130) (wInf.now + 86400))
  let to : Recipient := { recipientId := r.2.recipientId, assignment := .fungible 130 }
  let b :=
    (aliceInf.1.sendBegin wInf aliceO [(ifaId, [to])] false 1 1 (wInf.now + 3600)).toOption.get!
  let e := (b.1.sendEnd wInf aliceO b.2.txid).toOption.get!
  let g := (r.1.provideOutOfBandConsignment e.2.1 bobO (e.2.2.headD default).2).toOption.get!
  (g.1, e.2.1, r.2, e.1)
/-- The known circulating supply of the asset in a wallet. -/
def knownSupply (w : Wallet) : Option Nat := (w.db.asset? ifaId).bind (·.knownCirculatingSupply)
-- received for the first time, it is known from the consignment that 130 were issued
#guard knownSupply (got130 bob1).1 == some 130
def bobGot130 : Wallet × World × ReceiveData × Wallet := got130 bobIfa
-- imported before, 100 are known until the transfer with the inflation in its history settles
#guard knownSupply bobGot130.1 == some 100
def bobSettled130 : Wallet :=
  let acked := (bobGot130.2.2.2.provideOutOfBandAck bobGot130.2.1 aliceO
    bobGot130.2.2.1.recipientId).toOption.get!
  (bobGot130.1.refresh { acked.2.1 with chain := acked.2.1.chain.mine } bobO).toOption.get!.1
-- then 130
#guard knownSupply bobSettled130 == some 130 &&
  bobSettled130.assetBalance ifaId == ⟨130, 130, 130⟩

end Rgb.Examples.ContractsScenario
