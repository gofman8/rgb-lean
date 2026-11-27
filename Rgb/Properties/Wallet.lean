import Rgb.Lib.Receive

/-!
# Wallet: expected behaviour

Rules of the wallet library that hold for every input.
-/

namespace Rgb.Lib

/-- A fee rate is accepted exactly between 1 sat/vB and the `u64` bound of `rate * 250`. -/
theorem checkFeeRate_ok_iff (r : Nat) : checkFeeRate r = .ok () ↔ 1 ≤ r ∧ r * 250 ≤ Bound.u64 := by
  unfold checkFeeRate minFeeRate
  by_cases h1 : r < 1
  · simp [h1]; omega
  · by_cases h2 : r * 250 > Bound.u64
    · simp [h1, h2]; try omega
    · simp [h1, h2]; try omega

/-- The key checks come first: keys they refuse fail the wallet with their error. -/
theorem create_keysFirst (data : WalletData) (keys : SinglesigKeys) (e : Error)
    (hk : keys.buildDescriptors data.bitcoinNetwork = .error e) :
    Wallet.create data keys = .error e := by
  simp [Wallet.create, hk]; rfl

/-- A wallet with valid keys needs a positive allocation cap. -/
theorem create_noMaxAllocations (data : WalletData) (keys : SinglesigKeys)
    (d : WalletDescriptors × Bool) (hk : keys.buildDescriptors data.bitcoinNetwork = .ok d)
    (h : data.maxAllocationsPerUtxo = 0) :
    Wallet.create data keys = .error .noMaxAllocationsPerUtxo := by
  simp [Wallet.create, hk, h]; rfl

/-- A wallet with valid keys needs at least one schema. -/
theorem create_noSupportedSchemas (data : WalletData) (keys : SinglesigKeys)
    (d : WalletDescriptors × Bool) (hk : keys.buildDescriptors data.bitcoinNetwork = .ok d)
    (h0 : data.maxAllocationsPerUtxo ≠ 0) (h : data.supportedSchemas = []) :
    Wallet.create data keys = .error .noSupportedSchemas := by
  simp [Wallet.create, hk, h, h0]; rfl

/-- An allocation is never both settled and future. -/
theorem settled_not_future (a : LocalRgbAllocation) : a.settled = true → a.future = false := by
  intro h
  simp [LocalRgbAllocation.future, h]

/-- A failed allocation counts nowhere: not settled, not future, not held. -/
theorem failed_counts_nowhere (a : LocalRgbAllocation) (h : a.status = .failed) :
    a.settled = false ∧ a.future = false ∧ a.held = false := by
  simp [LocalRgbAllocation.settled, LocalRgbAllocation.future, LocalRgbAllocation.held, h]

/-- Final statuses are not waiting, and only pending statuses are refreshed. -/
theorem final_not_waiting (s : TransferStatus) : s.isFinal = true → s.isWaiting = false := by
  cases s <;> decide

/-- Waiting confirmations is pending but not fallible: such a transfer settles or
fails by its deadline, never by `fail_transfers`. -/
theorem waitingConfirmations_not_fallible :
    TransferStatus.waitingConfirmations.isPending = true ∧
      TransferStatus.waitingConfirmations.isFallible = false := by decide

/-- A receive without an asset keeps a fungible request and refuses rights. -/
theorem narrow_without_asset (n : UInt64) :
    Wallet.narrowAssignment none (.fungible n) = .ok (.fungible n) ∧
      Wallet.narrowAssignment none .linkRight = .error .invalidAssignment ∧
      Wallet.narrowAssignment none .any = .ok .any := by
  simp [Wallet.narrowAssignment]

/-- For every schema, `Any` narrows to an assignment the schema supports, or stays
`Any` where several kinds are possible (IFA, BFA). -/
theorem narrow_any (s : AssetSchema) :
    Wallet.narrowAssignment (some s) .any = .ok s.anyAssignment := by
  simp [Wallet.narrowAssignment]

/-- A UDA never takes a fungible amount, and only BFA takes mint rights. -/
theorem schema_capabilities :
    AssetSchema.uda.supportsAssignment (.fungible 1) = false ∧
      (AssetSchema.all.filter (·.supportsAssignment .mintRight)) = [.bfa] ∧
      (AssetSchema.all.filter (!·.allowedOnMainnet)) = [.ifa, .bfa] := by decide

end Rgb.Lib
