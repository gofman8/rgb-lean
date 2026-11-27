import Rgb.Consensus.Vm

/-!
# VM: expected behaviour of the sum opcodes

What a passing `svs`, `sas` or `sps` guarantees about the operation, for every
context: these are the conservation and issuance rules of the fungible schemas.
-/

namespace Rgb

/-- Output amounts accepted by the sum opcodes never contain zero. -/
theorem VmContext.outAmounts_no_zero (c : VmContext) (t : AssignmentType) (xs : List Nat)
    (h : c.outAmounts t = some xs) : 0 ∉ xs := by
  unfold VmContext.outAmounts at h
  split at h
  · simp at h; subst h; simp
  · simp at h
    obtain ⟨hnz, rfl⟩ := h
    simpa using hnz
  · simp at h

/-- A passing `svs` means the inputs and the outputs of the type sum to the same
amount, with no overflow (the transfer rule of the fungible schemas). -/
theorem exec_svs_next (c : VmContext) (s s' : VmState) (t : AssignmentType)
    (h : exec c s (.svs t) = .next s') :
    ∃ n, ((fungibleAmounts (c.prev t)).bind sumU64 = some n) ∧ ((c.outAmounts t).bind sumU64 = some n) := by
  simp only [exec] at h
  split at h
  · rename_i i o hi ho
    by_cases he : i == o
    · refine ⟨i, hi, ?_⟩
      have : i = o := by simpa using he
      rw [ho, this]
    · simp [he, VmState.halt] at h
  · simp [VmState.halt] at h

/-- A passing `sas` means the outputs of the type sum to `a64[0]`
(the issuance rule: genesis assigns exactly the issued supply). -/
theorem exec_sas_next (c : VmContext) (s s' : VmState) (t : AssignmentType)
    (h : exec c s (.sas t) = .next s') :
    ∃ v, s.a64 0 = some v ∧ (c.outAmounts t).bind sumU64 = some v := by
  simp only [exec] at h
  split at h
  · rename_i v o hv ho
    by_cases he : v == o
    · have : v = o := by simpa using he
      exact ⟨v, hv, by rw [ho, this]⟩
    · simp [he, VmState.halt] at h
  · simp [VmState.halt] at h

/-- A passing `sps` means the inputs of the type sum to `a64[0]`
(the burn and inflation rules). -/
theorem exec_sps_next (c : VmContext) (s s' : VmState) (t : AssignmentType)
    (h : exec c s (.sps t) = .next s') :
    ∃ v, s.a64 0 = some v ∧ (fungibleAmounts (c.prev t)).bind sumU64 = some v := by
  simp only [exec] at h
  split at h
  · rename_i v i hv hi
    by_cases he : v == i
    · have : v = i := by simpa using he
      exact ⟨v, hv, by rw [hi, this]⟩
    · simp [he, VmState.halt] at h
  · simp [VmState.halt] at h

/-- A failing opcode stops the VM with `st0 = false`. -/
theorem halt_stops (s : VmState) : s.halt = .stop { s with st0 := false } := rfl

/-- `test` continues exactly when `st0` holds. -/
theorem exec_test (c : VmContext) (s : VmState) :
    exec c s .test = if s.st0 then .next s else s.halt := rfl

end Rgb
