import Rgb.Lib.Issue

/-!
# Wallet scenarios: setup and issuance

A regtest wallet is funded on its vanilla keychain, goes online, creates
colored UTXOs and issues assets. Each check states an rgb-lib rule.
-/

namespace Rgb.Examples.WalletScenario

open Rgb Rgb.Lib

/-- Keys of a scenario wallet on `network`, generated from entropy named by `name`. -/
def keysOf (name : String) (network : BitcoinNetwork := .regtest) : SinglesigKeys :=
  .fromKeys (generateKeys network .taproot (Digest.of "scenario/entropy" [name]).fingerprint.toNat)

def dataOf (schemas : List AssetSchema := AssetSchema.all) : WalletData :=
  { bitcoinNetwork := .regtest, maxAllocationsPerUtxo := 5, supportedSchemas := schemas }

def alice0 : Wallet := (Wallet.create dataOf (keysOf "alice")).toOption.get!

-- wallet creation rules
#guard Wallet.create { dataOf with maxAllocationsPerUtxo := 0 } (keysOf "x") matches .error .noMaxAllocationsPerUtxo
#guard Wallet.create (dataOf []) (keysOf "x") matches .error .noSupportedSchemas
#guard Wallet.create { dataOf with bitcoinNetwork := .mainnet } (keysOf "x" .mainnet)
  matches .error (.cannotUseSchemaOnMainnet .ifa)
#guard (Wallet.create { dataOf [.nia, .uda, .cfa] with bitcoinNetwork := .mainnet }
  (keysOf "x" .mainnet)) matches .ok _
#guard (Wallet.create { dataOf with bitcoinNetwork := .mainnet, allowRecklessSchemas := true }
  (keysOf "x" .mainnet)) matches .ok _
-- the key checks come first: keys of another network, an xpub that does not parse
#guard Wallet.create { dataOf with maxAllocationsPerUtxo := 0 } (keysOf "x" .mainnet)
  matches .error .invalidBitcoinKeys
#guard Wallet.create (dataOf []) { keysOf "x" with accountXpubColored := "x-c" }
  matches .error (.invalidPubkey _)

/-- Fund Alice's first vanilla address with 100000 sats. -/
def fundAddr : Script × Wallet := alice0.getAddress
def world0 : World := { chain := ((Chain.mk [] [] 1700000000).fund fundAddr.1 100000 0).1, now := 1700000000 }
def alice1 : Wallet := fundAddr.2
def online : Wallet × Online × Result Unit := alice1.goOnline world0
def alice2 : Wallet := online.1
def onl : Online := online.2.1

-- going online checks the UTXO set
#guard online.2.2 == .ok ()
#guard (alice2.btcBalance world0.chain).vanilla == ⟨100000, 100000, 100000⟩
-- nothing can be issued before colored UTXOs exist
#guard (alice2.issueAssetNia 1 "USDT" "Tether" 2 [1000]).map (·.2.id) == .error .insufficientAllocationSlots

/-- Create the default 5 colored UTXOs of 1000 sats. -/
def created : Wallet × World × Nat := (alice2.createUtxos world0 onl false (feeRate := 1)).toOption.get!
def alice3 : Wallet := created.1
def world1 : World := { created.2.1 with chain := created.2.1.chain.mine }

#guard created.2.2 == 5
#guard (alice3.listUnspents).length == 5
-- with up_to, enough free UTXOs means nothing to do
#guard (alice3.createUtxosBegin world1 true (feeRate := 1)).map (·.2.txid) == .error .allocationsAlreadyAvailable
-- fee rate bounds
#guard (alice3.createUtxosBegin world1 false (feeRate := 0)).map (·.2.txid)
  == .error (.invalidFeeRate "value under minimum 1")
#guard (alice3.createUtxosBegin world1 false (size := some 0) (feeRate := 1)).map (·.2.txid)
  == .error .invalidAmountZero
-- a watch-only wallet cannot sign
#guard ({ alice2 with keys := { alice2.keys with mnemonic := none } }.createUtxos world0 onl false)
  matches .error .watchOnly

/-! ## Issuance -/

def issued : Wallet × DbAsset := (alice3.issueAssetNia 1700000700 "USDT" "Tether" 2 [600, 400]).toOption.get!
def alice4 : Wallet := issued.1
def usdt : String := issued.2.id

-- two allocations on two UTXOs, the whole supply settled and spendable
#guard alice4.assetBalance usdt == ⟨1000, 1000, 1000⟩
#guard ((alice4.listUnspents).filter (·.rgbAllocations.length > 0)).length == 2
#guard alice4.transferStatuses usdt == [(alice4.db.batchTransfers.getLast!.idx, .settled, .issuance)]
-- input checks, in rgb-lib's order
#guard (alice3.issueAssetNia 1 "USDT" "Tether" 2 []).map (·.2.id) == .error .noIssuanceAmounts
#guard (alice3.issueAssetNia 1 "USDT" "Tether" 2 [5, 0]).map (·.2.id) == .error .invalidAmountZero
#guard (alice3.issueAssetNia 1 "usdt" "Tether" 2 [5]).map (·.2.id)
  == .error (.invalidTicker "ticker needs to be all uppercase")
#guard (alice3.issueAssetNia 1 "USDT" "" 2 [5]).map (·.2.id) == .error (.invalidName "invalid name ")
#guard (alice3.issueAssetNia 1 "USDT" "Tether" 19 [5]).map (·.2.id)
  == .error (.invalidPrecision "precision is too high")
#guard (alice3.issueAssetNia 1 "USDT" "Tether" 2 [18446744073709551615, 1]).map (·.2.id)
  == .error .tooHighIssuanceAmounts
-- each amount needs its own UTXO
#guard (alice3.issueAssetNia 1 "USDT" "Tether" 2 [1, 1, 1, 1, 1, 1]).map (·.2.id) == .error .insufficientAllocationSlots
-- a schema the wallet does not support
#guard ((Wallet.create (dataOf [.nia]) (keysOf "b")).toOption.get!.issueAssetCfa 1 "C" none 0 [1]).map (·.2.id)
  == .error (.unsupportedSchema .cfa)

-- UDA: one token; IFA: inflation rights need empty UTXOs; BFA: mint rights
#guard ((alice3.issueAssetUda 1 "NFT" "Unique" none 0).map fun (w, a) => w.assetBalance a.id) == .ok ⟨1, 1, 1⟩
#guard ((alice3.issueAssetIfa 1 "INF" "Inflatable" 0 [100] [50] (linkRight := true)).map
  fun (_, a) => (a.initialSupply, a.maxSupply)) == .ok (100, some 150)
#guard (alice3.issueAssetIfa 1 "INF" "Inflatable" 0 [] []).map (·.2.id) == .error .noIssuanceAmounts
#guard (alice3.issueAssetBfa 1 "₿" "Bridged" 0 0 1 "0x0000000000000000000000000000000000000001").map (·.2.id)
  == .error .noMintRights
#guard (alice3.issueAssetBfa 1 "₿" "Bridged" 0 2 1 "0000").map (·.2.id)
  == .error (.invalidEvmContractAddress "address must start with 0x")
#guard ((alice3.issueAssetBfa 1 "₿" "Bridged" 0 2 1 "0x0000000000000000000000000000000000000001").map
  fun (w, a) => (w.listUnspents.filter (·.rgbAllocations.any (·.assignment == .mintRight))).length == 2 &&
    a.initialSupply == 0) == .ok true
-- the bridge contract address is read as its 20 bytes, from hex of either case
def bridgeAddr : String := "0x" ++ String.ofList (List.replicate 38 '0') ++ "Ff"
#guard ((alice3.issueAssetBfa 1 "₿" "Bridged" 0 2 1 bridgeAddr).map (·.2.bridgeLocation))
  == .ok (some (.evm ⟨1, ⟨List.replicate 19 0 ++ [255]⟩⟩))

/-! ## Pending vanilla transactions -/

-- a non-dry-run begin reserves its inputs until it ends or is aborted
def pendingUtxos : Wallet × Tx := (alice2.createUtxosBegin world0 false (feeRate := 1)).toOption.get!
#guard (pendingUtxos.1.listPendingVanillaTxs).map (·.2) == [.createUtxos]
-- reserved inputs cannot be used by another begin
#guard (pendingUtxos.1.createUtxosBegin world0 false (feeRate := 1)).map (·.2.txid)
  matches .error (.insufficientBitcoins _ _)
#guard ((pendingUtxos.1.abortPendingVanillaTx pendingUtxos.2.txid).map (·.listPendingVanillaTxs)) == .ok []
#guard (alice2.abortPendingVanillaTx pendingUtxos.2.txid).map (·.coloredNext) == .error .cannotAbortPendingVanillaTx

end Rgb.Examples.WalletScenario
