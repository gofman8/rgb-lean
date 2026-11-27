import Rgb.Lib.Operations
import Rgb.Examples.Wallet

/-!
# Inflate, burn and link scenarios

Alice issues an IFA asset with 100 units, an inflation allowance of 50 and a link
right, then inflates, burns and links. The histories the wallet builds are
checked against consensus with the IFA scripts.
-/

namespace Rgb.Examples.IfaOperations

open Rgb Rgb.Lib Rgb.Examples.WalletScenario

def ifaIssued : Wallet × DbAsset :=
  (alice3.issueAssetIfa 1700000700 "INF" "Inflatable" 0 [100] [50] (linkRight := true)).toOption.get!
def a0 : Wallet := ifaIssued.1
def inf : String := ifaIssued.2.id
def w0 : World := { world1 with now := 1700001000 }
def on0 : Wallet × Online × Result Unit := a0.goOnline w0
def a1 : Wallet := on0.1
def o : Online := on0.2.1

-- the allowance is not part of the balance; it is an inflation right
#guard a1.assetBalance inf == ⟨100, 100, 100⟩
#guard (a1.listUnspents.flatMap (·.rgbAllocations)).any (·.assignment == .inflationRight 50)

/-! ## Inflate -/

def inflated : Wallet × World × Txid := (a1.inflate w0 o inf [30]).toOption.get!
def w1 : World := { inflated.2.1 with chain := inflated.2.1.chain.mine }
def a2 : Wallet := (inflated.1.refresh w1 o).toOption.get!.1

-- 30 new units on a new output; 20 of the allowance remain
#guard a2.assetBalance inf == ⟨130, 130, 130⟩
#guard (a2.listUnspents.flatMap (·.rgbAllocations)).any (·.assignment == .inflationRight 20)
#guard ((a2.db.asset? inf).bind (·.knownCirculatingSupply)) == some 130
-- the history the wallet built is valid for the IFA scripts
def history : Consignment := (a2.stock.consign (a2.contractIdOf? inf).get! [] [] [] true).toOption.get!
#guard (history.validate true Schemas.ifaRules (w1.chain.resolver .bitcoinRegtest) { chainNet := .bitcoinRegtest }) matches .ok _
-- inflation above the remaining allowance, zero amounts, empty lists, other schemas
#guard (a2.inflate w1 o inf [21]) matches .error (.insufficientAssignments _ _)
#guard (a2.inflate w1 o inf [0]) matches .error .invalidAmountZero
#guard (a2.inflate w1 o inf []) matches .error .noInflationAmounts
#guard (alice4.goOnline w0 |>.1.inflate w0 (alice4.goOnline w0).2.1 usdt [5]) matches .error (.unsupportedInflation .nia)

/-! ## Burn -/

def burned : Wallet × World × Txid := (a2.burn w1 o inf 40).toOption.get!
def w2 : World := { burned.2.1 with chain := burned.2.1.chain.mine }
def a3 : Wallet := (burned.1.refresh w2 o).toOption.get!.1

-- 40 destroyed: the burn spends exactly 40 after a split, the change stays
#guard a3.assetBalance inf == ⟨90, 90, 90⟩
def history2 : Consignment := (a3.stock.consign (a3.contractIdOf? inf).get! [] [] [] true).toOption.get!
#guard (history2.validate true Schemas.ifaRules (w2.chain.resolver .bitcoinRegtest) { chainNet := .bitcoinRegtest }) matches .ok _
#guard (a3.burn w2 o inf 0) matches .error .noBurnAmount
#guard (a3.burn w2 o inf 5 (some "zz")) matches .error (.invalidBurnReason _)
#guard (a3.burn w2 o inf 5 (some "abcd")) matches .error (.invalidBurnReason "expected 32 bytes, got 2")
-- the reason is hex of either case
#guard (a3.burn w2 o inf 5 (some "ABCD"))
  matches .error (.invalidBurnReason "expected 32 bytes, got 2")
#guard (a3.burn w2 o inf 1000) matches .error (.insufficientAssignments _ _)

/-! ## Link -/

def child : Wallet × DbAsset :=
  (a3.issueAssetIfa w2.now "KID" "Child" 0 [5] [] (linkedFrom := some inf)).toOption.get!
def a4 : Wallet := child.1
def kid : String := child.2.id
def linked : Wallet × World × Txid := (a4.link w2 o inf kid).toOption.get!

-- the link right is spent and the asset records its link
#guard ((linked.1.db.asset? inf).bind (·.linkedToContract)) == some kid
#guard !((linked.1.listUnspents.flatMap (·.rgbAllocations)).any fun a => a.assignment == .linkRight && a.settled)
-- linking to itself, to an unknown contract, or to one not issued linked from this asset
#guard (a4.link w2 o inf inf) matches .error .cannotLinkToItself
#guard (a4.link w2 o inf "rgb:unknown") matches .error (.unknownLinkedContract _)
#guard (a4.link w2 o kid inf) matches .error (.invalidLinkedContract _ _)
-- a second link needs a second right
def w3 : World := { linked.2.1 with chain := linked.2.1.chain.mine }
#guard ((linked.1.refresh w3 o).toOption.get!.1.link w3 o inf kid) matches .error (.insufficientAssignments _ _)

/-! ## Listing -/

-- the issuance, the inflation, the burn and the link are listed with their kinds
#guard (linked.1.transferStatuses inf).map (·.2.2) == [.issuance, .inflation, .burn, .link]
-- each with what it asked for; the inflation pays an output of the wallet, as a recipient
#guard ((linked.1.listTransfers (some inf)).map fun l => l.map (·.requestedAssignment))
  == .ok [none, some (.fungible 30), some (.fungible 40), some .linkRight]
#guard ((a2.listTransfers (some inf)).map fun l => l.map (·.receiveUtxo))
  == .ok [none, some ⟨inflated.2.2, 1⟩]

end Rgb.Examples.IfaOperations
