import Rgb.Commit.Dbc
import Rgb.Consensus.Bundle

/-!
# Commitments: expected behaviour
-/

namespace Rgb

/-- The bundle id depends on the input map only: revealing or hiding known
transitions never changes the MPC message of a bundle. -/
theorem TransitionBundle.bundleId_inputMap (a b : TransitionBundle) (h : a.inputMap = b.inputMap) :
    a.bundleId = b.bundleId := by
  simp [TransitionBundle.bundleId, h]

/-- The contract id is the id of its genesis. -/
theorem Genesis.contractId_eq_id (g : Genesis) : g.contractId.d = g.id.d := rfl

/-- A passing opret verification means the first `OP_RETURN` output of the
witness carries exactly the commitment. -/
theorem opret_verify_ok (c : Digest) (tx : Tx) (h : DbcProof.opret.verify c tx = .ok ()) :
    ∃ o, tx.outputs.find? (·.script.isOpReturn) = some o ∧ o.script = .opReturn (some c) := by
  simp only [DbcProof.verify] at h
  split at h
  · simp at h
  · rename_i o ho
    split at h
    · rename_i c' hs
      split at h
      · rename_i hc
        exact ⟨o, ho, by rw [hs, eq_of_beq hc]⟩
      · simp at h
    · simp at h

/-- A passing tapret verification means the first taproot output's key is the
internal key tweaked with a tree that holds the commitment leaf. -/
theorem tapret_verify_ok (c : Digest) (tx : Tx) (p : TapretProof)
    (h : (DbcProof.tapret p).verify c tx = .ok ()) :
    ∃ o q, tx.outputs.find? (·.script.isTaproot) = some o ∧ p.outputKey c = .ok q ∧ o.script = .p2tr q := by
  simp only [DbcProof.verify] at h
  split at h
  · simp at h
  · rename_i o ho
    cases hk : p.outputKey c with
    | error e => simp [hk, bind, Except.bind] at h
    | ok q =>
      refine ⟨o, q, ho, rfl, ?_⟩
      simp only [hk, bind, Except.bind] at h
      split at h
      · rename_i hs
        exact eq_of_beq hs
      · simp at h

end Rgb
