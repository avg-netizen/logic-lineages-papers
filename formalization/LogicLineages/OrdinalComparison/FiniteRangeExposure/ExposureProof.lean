module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.SyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- The finite maximum is enough because every retained inner kernel is an
unsigned iterate and hence cannot lower the current actual argument. -/
theorem sourceExposure : Targets.SourceExposure := by
  intro D n m
  induction m with
  | zero =>
      intro c t j hD ht
      simpa [exposureTail,exposureWord,exposurePrefix,SourceRangeExpansion.expansionWord] using
        (SourceRangeExpansion.Proof.sourceBlockExpansion D n c t j hD ht)
  | succ m ih =>
      intro c t j hD ht
      have hStepTail : SourceRangeExpansion.expansionTail (n+m+1) c j ≤ t :=
        (Nat.le_max_left _ _).trans ht
      have hRestTail : exposureTail n m c j ≤ t := (Nat.le_max_right _ _).trans ht
      have hStep := SourceRangeExpansion.Proof.sourceBlockExpansion D (n+m+1) c t j (by omega) hStepTail
      let entry := sourceSignedValue (n+m+4) (c+(n+m+4)) 0 t
      have hEntry : t ≤ entry := iterate_self_le (fun z => (self_lt_Phi z).le) _ t
      have hChild := ih c entry j (by omega) (hRestTail.trans hEntry)
      have hFirst : LetterDomain (kernelLetter (n+m+4) (c+(n+m+4)) 0) t := hStep.2.1.1
      have hValue : sourceSignedValue (n+m+4) c j t = sourceSignedValue (n+m+3) c j entry := by
        simpa [SourceRangeExpansion.expansionWord,SourceRangeExpansion.lowerHead,
          wordValue,letterValue,kernelLetter,entry,Nat.add_assoc] using hStep.2.2
      refine ⟨hStep.1,?_,?_⟩
      · change LetterDomain (kernelLetter (n+m+4) (c+(n+m+4)) 0) t ∧
          WordDomain (exposureWord n m c j) entry
        exact ⟨hFirst,hChild.2.1⟩
      · change sourceSignedValue (n+m+4) c j t = wordValue (exposureWord n m c j) entry
        exact hValue.trans hChild.2.2

end LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
