module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
open PolynomialGraphCompletion

theorem specialize_eval (x n : Nat) (p : Formula) (ν : Nat → Nat) :
    Formula.eval ν (specialize x n p) ↔ Formula.eval (Function.update ν x n) p := by
  induction p with
  | bot => rfl
  | top => rfl
  | atom a =>
      cases a with
      | nonnegative r =>
          change (0 ≤ RowValue (specializeRow x n r) ν) ↔
            0 ≤ RowValue r (Function.update ν x n)
          rw [rowSubstitution x n r ν]
      | divisible m r =>
          change (((m+1 : Nat) : Int) ∣ RowValue (specializeRow x n r) ν) ↔
            ((m+1 : Nat) : Int) ∣ RowValue r (Function.update ν x n)
          rw [rowSubstitution x n r ν]
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | disj p q ihp ihq => exact or_congr ihp ihq

theorem specialize_domains (x n : Nat) (p : Formula) (ν : Nat → Nat) :
    Formula.meaningful p (Function.update ν x n) ↔
      removedDomains x n p = true ∧ Formula.meaningful (specialize x n p) ν := by
  change (∀ t ∈ p.tokens, WordDomain t.2 (Function.update ν x n t.1)) ↔
    ((p.tokens.all (fun t => if t.1 = x then wordDomain t.2 n else true)) = true ∧
      ∀ t ∈ (specialize x n p).tokens, WordDomain t.2 (ν t.1))
  rw [List.all_eq_true, exactSupport x n p]
  constructor
  · intro h
    constructor
    · intro t ht
      by_cases hx : t.1 = x
      · have hd : WordDomain t.2 n := by
          simpa [Function.update_apply, hx] using h t ht
        simpa [hx] using (wordDomainCorrect t.2 n).mpr hd
      · simp [hx]
    · intro t ht
      obtain ⟨hp, hne⟩ := List.mem_filter.mp ht
      have hx : t.1 ≠ x := by simpa using hne
      simpa only [Function.update_of_ne hx] using h t hp
  · rintro ⟨hd, hr⟩ t ht
    by_cases hx : t.1 = x
    · have hw : wordDomain t.2 n = true := by simpa [hx] using hd t ht
      have hv := (wordDomainCorrect t.2 n).mp hw
      simpa [Function.update_apply, hx] using hv
    · have hp : t ∈ p.tokens.filter (fun t => t.1 != x) :=
        List.mem_filter.mpr ⟨ht, by simp [hx]⟩
      simpa only [Function.update_of_ne hx] using hr t hp

theorem formulaSubstitution : Targets.FormulaSubstitution := by
  intro x n p ν
  exact ⟨specialize_eval x n p ν, specialize_domains x n p ν⟩

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
