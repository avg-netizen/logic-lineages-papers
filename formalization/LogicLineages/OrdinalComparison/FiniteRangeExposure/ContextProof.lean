module
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.ExposureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
open PolynomialGraphCompletion WordGuardCompletion
open RangePhiFactorization.Proof

theorem contextExposure : Targets.ContextExposure := by
  intro D A S n m c j hA hS hD x hx
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A (exposureTail n m c j) x hA
    ((Nat.le_max_left _ _).trans hx)
  have hHead := sourceExposure D n m c (wordValue A x) j hD hAt.2
  have hAd : LetterAllowed D (kernelLetter (n+m+3) c j) := by
    simp [kernelLetter,LetterAllowed,hD]
  have hOldAllowed := word_allowed_append D (A++[kernelLetter (n+m+3) c j]) S
    (word_allowed_append D A _ hA (singleton_allowed D _ hAd)) hS
  have hOld := WordGuardCompletion.Proof.wordTailCorrect D (A++[kernelLetter (n+m+3) c j]++S) x
    hOldAllowed ((Nat.le_max_right _ _).trans hx)
  have hNewAllowed := word_allowed_append D (A++exposureWord n m c j) S
    (word_allowed_append D A _ hA (prefixSyntax D n m c j hD).2.1) hS
  have hPrefixDom : WordDomain (A++exposureWord n m c j) x :=
    (WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hAt.1,hHead.2.1⟩
  have hPrefix : wordValue (A++[kernelLetter (n+m+3) c j]) x =
      wordValue (A++exposureWord n m c j) x := by
    rw [WordAlgebraProof.wordValue_append,WordAlgebraProof.wordValue_append]
    exact hHead.2.2
  have hSuffix := ((WordAlgebraProof.wordDomain_append (A++[kernelLetter (n+m+3) c j]) S x).mp hOld.1).2
  have hNewSuffix : WordDomain S (wordValue (A++exposureWord n m c j) x) := by
    rw [←hPrefix]
    exact hSuffix
  refine ⟨hNewAllowed,hOld.1,
    (WordAlgebraProof.wordDomain_append (A++exposureWord n m c j) S x).mpr ⟨hPrefixDom,hNewSuffix⟩,?_⟩
  rw [WordAlgebraProof.wordValue_append (A++[kernelLetter (n+m+3) c j]),
    WordAlgebraProof.wordValue_append (A++exposureWord n m c j),hPrefix]

end LogicLineages.OrdinalComparison.FiniteRangeExposure.Proof
