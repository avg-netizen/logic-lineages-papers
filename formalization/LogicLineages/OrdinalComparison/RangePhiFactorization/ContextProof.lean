module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.HeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem contextFactorization : Targets.ContextFactorization := by
  intro D A S a hA hS ha hr x hx
  have hp := prefixFactorization D A a x hA ha hr ((Nat.le_max_left _ _).trans hx)
  have hOld : WordAllowed D ((A++[a])++S) :=
    word_allowed_append D _ S (word_allowed_append D A [a] hA (singleton_allowed D a ha)) hS
  have hOriginal := WordGuardCompletion.Proof.wordTailCorrect D (A++[a]++S) x
    (by simpa only [List.append_assoc] using hOld) ((Nat.le_max_right _ _).trans hx)
  have hNew : WordAllowed D ((A++[predecessorHead a,phiLetter])++S) :=
    word_allowed_append D _ S (word_allowed_append D A _ hA (factored_allowed D a ha hr)) hS
  have hOldDomain : WordDomain ((A++[a])++S) x := by
    simpa only [List.append_assoc] using hOriginal.1
  have hSuffix := ((WordAlgebraProof.wordDomain_append (A++[a]) S x).mp hOldDomain).2
  have hNewSuffix : WordDomain S (wordValue (A++[predecessorHead a,phiLetter]) x) := by
    rw [←hp.2.2]
    exact hSuffix
  have hNewDomain := (WordAlgebraProof.wordDomain_append (A++[predecessorHead a,phiLetter]) S x).mpr
    ⟨hp.2.1,hNewSuffix⟩
  refine ⟨by simpa only [List.append_assoc] using hNew,hOriginal.1,
    by simpa only [List.append_assoc] using hNewDomain,?_⟩
  have he : wordValue ((A++[a])++S) x = wordValue ((A++[predecessorHead a,phiLetter])++S) x := by
    rw [WordAlgebraProof.wordValue_append (A++[a]),
      WordAlgebraProof.wordValue_append (A++[predecessorHead a,phiLetter]),hp.2.2]
  simpa only [List.append_assoc] using he

end LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
