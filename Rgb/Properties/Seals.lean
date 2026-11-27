import Rgb.Consensus.Bundle
import Rgb.Consensus.Occurrences

/-!
# Seals, ids and occurrences: expected behaviour

Statements about the model that hold for every input.
-/

namespace Rgb

/-- An occurrence accepts exactly the counts between its minimum and maximum. -/
theorem Occurrences.check_ok_iff (o : Occurrences) (n : Nat) :
    o.check n = .ok () ↔ o.minValue ≤ n ∧ n ≤ o.maxValue := by
  unfold Occurrences.check
  by_cases h : o.minValue ≤ n ∧ n ≤ o.maxValue
  · simp [h.1, h.2]
  · constructor
    · intro hc
      by_cases h1 : o.minValue ≤ n <;> by_cases h2 : n ≤ o.maxValue <;> simp_all
    · intro hc; exact absurd hc h

/-- Revealing a seal never changes the concealed form. -/
theorem BuilderSeal.reveal_toSecret {σ : Type} [SealKind σ] (b : BuilderSeal σ) (s : σ) :
    (b.reveal s).toSecret = b.toSecret := by
  cases b with
  | revealed x => rfl
  | concealed c =>
    simp only [BuilderSeal.reveal]
    split
    · next h => simp [BuilderSeal.toSecret, eq_of_beq h]
    · rfl

/-- Concealing a seal keeps its concealed form. -/
theorem BuilderSeal.conceal_toSecret {σ : Type} [SealKind σ] (b : BuilderSeal σ) :
    b.conceal.toSecret = b.toSecret := rfl

/-- A witness closes a seal only by spending the seal's outpoint. -/
theorem closesSeal_spends (w : Tx) (s : GraphSeal) (h : closesSeal w s = .ok ()) :
    ∃ o, s.outpoint? = some o ∧ w.spends o = true := by
  unfold closesSeal at h
  cases hs : s.outpoint? with
  | none => simp [hs] at h
  | some o =>
    simp only [hs] at h
    by_cases hw : w.spends o = true
    · exact ⟨o, rfl, hw⟩
    · simp [hw] at h

/-- A seal pointing to the witness transaction can never be closed: it has no
outpoint yet. -/
theorem closesSeal_witnessTx (w : Tx) (vout : UInt32) (blinding : UInt64) :
    closesSeal w (GraphSeal.witnessVout vout blinding) = .error .noWitnessTxid := rfl

/-- Revealing a seal inside a bundle keeps the bundle id. -/
theorem TransitionBundle.revealSeal_bundleId (b : TransitionBundle) (s : GraphSeal) :
    (b.revealSeal s).bundleId = b.bundleId := rfl

private theorem items_mapSeals_toSecret {σ : Type} [SealKind σ] (ta : TypedAssigns σ)
    (f : BuilderSeal σ → BuilderSeal σ) (hf : ∀ b, (f b).toSecret = b.toSecret) :
    (ta.mapSeals f).items.map (fun p => (p.1.toSecret, p.2)) =
      ta.items.map (fun p => (p.1.toSecret, p.2)) := by
  cases ta with
  | declarative l => simp [TypedAssigns.mapSeals, TypedAssigns.items, hf]
  | fungible l => simp [TypedAssigns.mapSeals, TypedAssigns.items, hf]
  | structured l => simp [TypedAssigns.mapSeals, TypedAssigns.items, hf]

private theorem leaves_eq {σ : Type} [SealKind σ] (ta : TypedAssigns σ) (ty : AssignmentType) :
    ta.items.map (fun p => encode ty ++ encode p.2 ++ encode p.1.toSecret) =
      (ta.items.map (fun p => (p.1.toSecret, p.2))).map
        (fun q => encode ty ++ encode q.2 ++ encode q.1) := by
  simp

/-- Concealing every seal of a transition keeps its id: the id commits to
concealed seals only. -/
theorem Transition.id_conceal (t : Transition) :
    { t with assignments := t.assignments.mapValues (TypedAssigns.mapSeals BuilderSeal.conceal) }.id
      = t.id := by
  have key : ∀ (l : List (AssignmentType × TypedAssigns GraphSeal)),
      (l.map (fun (k, v) => (k, TypedAssigns.mapSeals BuilderSeal.conceal v))).flatMap
          (fun (ty, ta) => ta.items.map fun (s, st) => encode ty ++ encode st ++ encode s.toSecret)
        = l.flatMap
          (fun (ty, ta) => ta.items.map fun (s, st) => encode ty ++ encode st ++ encode s.toSecret) := by
    intro l
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      obtain ⟨ty, ta⟩ := hd
      simp only [List.map_cons, List.flatMap_cons, ih]
      congr 1
      have h1 := leaves_eq (ta.mapSeals BuilderSeal.conceal) ty
      have h2 := leaves_eq ta ty
      have h3 := items_mapSeals_toSecret ta BuilderSeal.conceal (fun b => rfl)
      rw [h1, h2, h3]
  simp only [Transition.id, assignmentLeaves, OrdMap.mapValues]
  rw [key]

end Rgb
