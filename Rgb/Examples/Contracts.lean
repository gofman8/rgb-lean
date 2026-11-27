import Rgb.Lib.Contracts
import Rgb.Examples.Transfer

/-!
# Contract import and export, fee estimation
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
  (Wallet.create { dataOf [.nia] with bitcoinNetwork := .mainnet } (keysOf "m")).toOption.get!
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

end Rgb.Examples.ContractsScenario
