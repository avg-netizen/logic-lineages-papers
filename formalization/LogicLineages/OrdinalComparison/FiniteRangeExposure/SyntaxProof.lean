module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.Targets
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.HeadProof
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

private theorem prefixFacts : ∀ D n m c : Nat, n+m+3 ≤ D →
    WordAllowed D (exposurePrefix n m c) ∧ (exposurePrefix n m c).length = m+1 ∧
    counterNodes (exposurePrefix n m c) = 0 ∧
    ∀ a ∈ exposurePrefix n m c, a.1=3 ∧ n+3 ≤ a.2.1 ∧ a.2.1 ≤ n+m+3 ∧ a.2.2.2=0 := by
  intro D n m
  induction m with
  | zero =>
      intro c hD
      refine ⟨?_,rfl,?_,?_⟩
      · intro a ha
        have he := List.mem_singleton.mp ha
        subst a
        simp [kernelLetter,LetterAllowed] at *
        omega
      · simp [exposurePrefix,counterNodes,kernelLetter]
      · intro a ha
        have he := List.mem_singleton.mp ha
        subst a
        simp [kernelLetter]
  | succ m ih =>
      intro c hD
      have hi := ih c (by omega)
      refine ⟨?_,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [kernelLetter,LetterAllowed]
          omega
        · exact hi.1 a ha
      · simp [exposurePrefix,hi.2.1]
      · simpa [exposurePrefix,counterNodes,kernelLetter] using hi.2.2.1
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [kernelLetter]
          omega
        · have hh := hi.2.2.2 a ha
          exact ⟨hh.1,hh.2.1,by omega,hh.2.2.2⟩

theorem prefixSyntax : Targets.PrefixSyntax := by
  intro D n m c j hD
  have hp := prefixFacts D n m c hD
  have hLow : WordAllowed D [SourceRangeExpansion.lowerHead n c j] := by
    intro a ha
    exact (SourceRangeExpansion.Proof.expansionSyntax D n c j (by omega)).1 a
      (List.mem_cons_of_mem _ ha)
  exact ⟨hp.1,RangePhiFactorization.Proof.word_allowed_append D _ _ hp.1 hLow,
    hp.2.1,hp.2.2.1,hp.2.2.2⟩

end LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
