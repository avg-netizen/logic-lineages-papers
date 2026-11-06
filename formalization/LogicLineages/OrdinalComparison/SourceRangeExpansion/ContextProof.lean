module
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.HeadProof
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open RangePhiFactorization.Proof

theorem contextExpansion : Targets.ContextExpansion := by
  intro D A S n c j hA hS hD x hx
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A (expansionTail n c j) x hA
    ((Nat.le_max_left _ _).trans hx)
  have hHead := sourceBlockExpansion D n c (wordValue A x) j hD hAt.2
  have hAd : LetterAllowed D (kernelLetter (n+3) c j) := by
    simp [kernelLetter,LetterAllowed,hD]
  have hOldAllowed := word_allowed_append D (A++[kernelLetter (n+3) c j]) S
    (word_allowed_append D A _ hA (singleton_allowed D _ hAd)) hS
  have hOld := WordGuardCompletion.Proof.wordTailCorrect D (A++[kernelLetter (n+3) c j]++S) x
    hOldAllowed ((Nat.le_max_right _ _).trans hx)
  have hNewAllowed := word_allowed_append D (A++expansionWord n c j) S
    (word_allowed_append D A _ hA (expansionSyntax D n c j hD).1) hS
  have hPrefixDom : WordDomain (A++expansionWord n c j) x :=
    (WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hAt.1,hHead.2.1⟩
  have hPrefix : wordValue (A++[kernelLetter (n+3) c j]) x =
      wordValue (A++expansionWord n c j) x := by
    rw [WordAlgebraProof.wordValue_append,WordAlgebraProof.wordValue_append]
    exact hHead.2.2
  have hSuffix := ((WordAlgebraProof.wordDomain_append (A++[kernelLetter (n+3) c j]) S x).mp hOld.1).2
  have hNewSuffix : WordDomain S (wordValue (A++expansionWord n c j) x) := by
    rw [←hPrefix]
    exact hSuffix
  refine ⟨hNewAllowed,hOld.1,
    (WordAlgebraProof.wordDomain_append (A++expansionWord n c j) S x).mpr ⟨hPrefixDom,hNewSuffix⟩,?_⟩
  rw [WordAlgebraProof.wordValue_append (A++[kernelLetter (n+3) c j]),
    WordAlgebraProof.wordValue_append (A++expansionWord n c j),hPrefix]

end LogicLineages.OrdinalComparison.SourceRangeExpansion.Proof
