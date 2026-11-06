module
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.KernelOrderProof
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

theorem equalRankWordGuardCorrect : Targets.EqualRankWordGuardCorrect := by
  intro D A B hA hB d c e j k hd _hD x y hx hy
  have hAx : reachTail A (equalityTail d c e j k) ≤ x :=
    (Nat.le_max_left _ _).trans hx
  have hBy : reachTail B (equalityTail d c e j k) ≤ y :=
    (Nat.le_max_right _ _).trans hy
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA hAx
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB hBy
  have hdomains := UniformCompletion.Proof.effectiveEqualityTail d c e j k hd
    (wordValue A x) (wordValue B y) hAt.2 hBt.2
  have hleft : wordValue (A ++ [kernelLetter d c j]) x =
      sourceSignedValue d c j (wordValue A x) := by
    rw [WordAlgebraProof.wordValue_append]
    rfl
  have hright : wordValue (B ++ [kernelLetter d e k]) y =
      sourceSignedValue d e k (wordValue B y) := by
    rw [WordAlgebraProof.wordValue_append]
    rfl
  have hlt := kernelOrderCorrect d c e j k hd (wordValue A x) (wordValue B y)
    hAt.2 hBt.2
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply (WordAlgebraProof.wordDomain_append A _ x).mpr
    refine ⟨hAt.1,?_⟩
    exact ⟨⟨hdomains.1,hdomains.2.2.1⟩,trivial⟩
  · apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    refine ⟨hBt.1,?_⟩
    exact ⟨⟨hdomains.2.1,hdomains.2.2.2.1⟩,trivial⟩
  · rw [hleft,hright]
    exact hlt
  · rw [hleft,hright]
    exact hdomains.2.2.2.2
  · rw [hleft,hright,le_iff_lt_or_eq,hlt,hdomains.2.2.2.2]

end LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
