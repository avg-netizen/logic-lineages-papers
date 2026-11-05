module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphExistentialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
open NormalForm PlainParameterDecision

theorem exactFixedNames : PlainParameterDecisionTargets.ExactFixedNames := by
  intro xs p i
  simp [fixedNames]

theorem pin_eval (i n : Nat) (σ : Nat → Nat) : (pin i n).eval σ ↔ σ i = n :=
  SourceTermGraphSemanticProof.numeral_equation i n σ

private theorem pins_eval (names values : List Nat) (σ : Nat → Nat) :
    (names.foldr (fun i rest => Formula.conjunction (pin i (valuation values i)) rest) .truth).eval σ ↔
      ∀ i ∈ names, σ i = valuation values i := by
  induction names with
  | nil => simp [Formula.eval]
  | cons i names ih =>
      simp only [List.foldr_cons, Formula.eval, pin_eval, ih, List.mem_cons, forall_eq_or_imp]

theorem exactFrame : PlainParameterDecisionTargets.ExactFrame := by
  intro xs values p σ
  simp only [frame, Formula.eval, pins_eval]
  apply and_congr_right
  intro _
  constructor
  · intro h i hi hn
    exact h i ((exactFixedNames xs p i).mpr ⟨hi, hn⟩)
  · intro h i hi
    obtain ⟨hp, hn⟩ := (exactFixedNames xs p i).mp hi
    exact h i hp hn

theorem actualParameterizedExistential : PlainParameterDecisionTargets.ActualParameterizedExistential := by
  intro xs values p
  rw [SourceTermGraphExistentialProof.existsPrefix_iff_frame]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hp, hf⟩ := (exactFrame xs values p σ).mp hσ
    let μ : Nat → Nat := fun i => if i ∈ xs then σ i else valuation values i
    refine ⟨μ, ?_, ?_⟩
    · intro i hi
      simp only [μ, if_neg hi]
    · apply (SourceTermGraphSupportProof.formula_eval_congr p σ μ ?_).mp hp
      intro i hi
      by_cases hx : i ∈ xs
      · simp only [μ, if_pos hx]
      · simp only [μ, if_neg hx]
        exact hf i hi hx
  · rintro ⟨σ, hf, hp⟩
    exact ⟨σ, (exactFrame xs values p σ).mpr ⟨hp, fun i _ hi => hf i hi⟩⟩

theorem forallPrefix_not_exists (ν : Nat → Nat) (xs : List Nat) (p : Formula) :
    forallPrefix ν xs p ↔ ¬existsPrefix ν xs (.negative p) := by
  classical
  induction xs generalizing ν with
  | nil => simp only [forallPrefix, existsPrefix, Formula.eval, not_not]
  | cons i xs ih =>
      simp only [forallPrefix, existsPrefix, not_exists, ← ih]

theorem actualParameterizedUniversal : PlainParameterDecisionTargets.ActualParameterizedUniversal := by
  intro xs values p
  rw [actualParameterizedExistential]
  exact (forallPrefix_not_exists (valuation values) xs p).symm

private theorem pin_plain (i n : Nat) : MaximalPlainBranch.isPlain (pin i n) = true := by
  simp [pin, SourceTermGraph.equation, SourceTermGraph.numeralRow, SourceTermGraph.negateRow,
    MaximalPlainBranch.isPlain, LinearRows.atoms, Atom.row, PlainPhiDominance.isPlain]

private theorem pins_plain (names values : List Nat) :
    MaximalPlainBranch.isPlain
      (names.foldr (fun i rest => Formula.conjunction (pin i (valuation values i)) rest) .truth) = true := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      simpa only [List.foldr_cons, MaximalPlainBranch.isPlain, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨pin_plain i (valuation values i), ih⟩

theorem preservePlain : PlainParameterDecisionTargets.PreservePlain := by
  intro xs values p hp
  simpa only [frame, MaximalPlainBranch.isPlain, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨hp, pins_plain (fixedNames xs p) values⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
