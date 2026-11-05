module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof

private theorem fold_all_iff {α : Type*} (f : α → Bool) (xs : List α) :
    xs.foldr (fun x b => f x && b) true = true ↔ ∀ x ∈ xs, f x = true := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem valid_monomial_iff (n : Nat) (m : MonomialCode) :
    SeededInputCode.validMonomial n m = true ↔ ∀ i, m.2.2 = some i → i < n := by
  unfold SeededInputCode.validMonomial
  cases h : m.2.2 <;> simp [h]

theorem exactWellFormed : Targets.ExactWellFormed := by
  intro c
  simp only [validSystem, fold_all_iff, validRow, valid_monomial_iff, WellFormedCode]

theorem exactQueryCalibration : Targets.ExactQueryCalibration := by
  intro strict n s
  have h := SeededSystemCode.Proof.exactQueryPairs n s
  cases strict with
  | false =>
      simp only [sourcePair, queryCode, Bool.false_eq_true, ↓reduceIte]
      rw [h.2.1, h.2.2]
      rfl
  | true =>
      simp only [sourcePair, queryCode, ↓reduceIte]
      rw [h.1, h.2.2]
      rfl

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof
