import Rgb.Lib.NoWallet

/-!
# EVM reads: expected behaviour
-/

namespace Rgb.Lib.Evm

/-- A lock is confirmed exactly when the bridge records it in a block before the one the
mint commits to. -/
theorem mintLockStatusOf_confirmed (r : Option Nat) (beforeBlock fin : Nat) :
    mintLockStatusOf r beforeBlock fin = .confirmed ↔ ∃ b, r = some b ∧ b < beforeBlock := by
  cases r with
  | none => simp only [mintLockStatusOf]; split <;> simp
  | some b => simp only [mintLockStatusOf]; split <;> simp_all

/-- A lock is pending exactly when it is not recorded and the block after the finalized one
is still before the block the mint commits to. -/
theorem mintLockStatusOf_pending (r : Option Nat) (beforeBlock fin : Nat) :
    mintLockStatusOf r beforeBlock fin = .pending ↔ r = none ∧ satAdd fin 1 < beforeBlock := by
  cases r with
  | none => simp only [mintLockStatusOf]; split <;> simp_all <;> omega
  | some b => simp only [mintLockStatusOf]; split <;> simp

/-- `mint_begin` accepts exactly the blocks that leave a block for the lock after the latest one
and lie from `minMintLockBlocks` to `maxMintLockBlocks` blocks after it. -/
theorem checkMintBeforeBlock_ok_iff (bb latest : Nat) (c : EvmChain) :
    checkMintBeforeBlock bb latest c = .ok () ↔
      satAdd latest 1 < bb ∧ satAdd latest c.minMintLockBlocks ≤ bb ∧
        bb ≤ satAdd latest c.maxMintLockBlocks := by
  unfold checkMintBeforeBlock
  by_cases h1 : bb ≤ satAdd latest 1 <;> by_cases h2 : bb < satAdd latest c.minMintLockBlocks <;>
    by_cases h3 : bb > satAdd latest c.maxMintLockBlocks <;>
    simp [h1, h2, h3, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, bind,
      Except.bind] <;> omega

theorem attemptsMade_go_length (k : Nat) (l : List Attempt) (hk : k ≤ rpcRetries) :
    (attemptsMade.go k l).length ≤ rpcRetries + 1 - k := by
  induction l generalizing k with
  | nil => simp [attemptsMade.go]
  | cons a rest ih =>
    simp only [attemptsMade.go]
    split
    · simp; omega
    · rename_i h
      have hne : k ≠ rpcRetries := by intro he; simp [he] at h
      have := ih (k + 1) (by omega)
      simp; omega

/-- A request is sent at most `rpcRetries + 1` times. -/
theorem attemptsMade_length (outcomes : List Attempt) :
    (attemptsMade outcomes).length ≤ rpcRetries + 1 :=
  attemptsMade_go_length 0 outcomes (Nat.zero_le _)

theorem attemptsMade_go_prefix (k : Nat) (l : List Attempt) : attemptsMade.go k l <+: l := by
  induction l generalizing k with
  | nil => simp [attemptsMade.go]
  | cons a rest ih =>
    simp only [attemptsMade.go]
    split
    · exact List.prefix_iff_eq_take.mpr (by simp)
    · exact List.cons_prefix_cons.mpr ⟨rfl, ih (k + 1)⟩

/-- The attempts made are the first outcomes, in order. -/
theorem attemptsMade_prefix (outcomes : List Attempt) : attemptsMade outcomes <+: outcomes :=
  attemptsMade_go_prefix 0 outcomes

/-- A checked client is connected to the chain it was asked for. -/
theorem checkedEvmClient_chainId (net : EvmNet) (urls : EvmRpcUrls) (id : Nat) (n : EvmNode)
    (h : checkedEvmClient net urls id = .ok n) : n.chainId = .ok id := by
  unfold checkedEvmClient evmClient at h
  cases hl : urls.lookup id with
  | none => simp [hl, bind, Except.bind] at h
  | some url =>
    simp only [hl, bind, Except.bind] at h
    cases hc : (net url).chainId with
    | error e => simp [hc] at h
    | ok actual =>
      simp only [hc] at h
      by_cases he : actual = id
      · subst he
        simp [pure, Except.pure] at h
        subst h
        exact hc
      · simp [he, throw, throwThe, MonadExceptOf.throw] at h

end Rgb.Lib.Evm

namespace Rgb.Lib.NoWallet

/-- A witness mined at the safe height has exactly `minConfirmations` confirmations. -/
theorem safeHeightFor_confirmations (tip m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ tip) :
    tip - safeHeightFor tip m + 1 = m := by
  unfold safeHeightFor; omega

end Rgb.Lib.NoWallet
