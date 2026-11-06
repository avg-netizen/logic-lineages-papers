module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.KernelProof
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem mixedQuadraticGuard : Targets.MixedQuadraticGuard := by
  intro D A B hA hB m c j k a b hD x y hx hy
  have hRetained := retainedWord_allowed D A 0 m c hA (by omega)
  have hExp := FiniteRangeExposure.Proof.contextExposure D A [shiftLetter a] 0 m c j
    hA (shift_allowed D a) (by omega) x ((Nat.le_max_left _ _).trans hx)
  have hs := QuadraticWordGuardCompletion.Proof.quadraticWordGuardCorrect D
    (retainedWord A 0 m c) B hRetained hB (j-(((c+1)/2 : Nat) : Int)) k a b x y
    ((Nat.le_max_right _ _).trans hx) ((Nat.le_max_right _ _).trans hy)
  have hOld : WordDomain (A++[kernelLetter (m+3) c j,shiftLetter a]) x := by
    simpa [List.append_assoc] using hExp.2.1
  have hEq : wordValue (A++[kernelLetter (m+3) c j,shiftLetter a]) x =
      wordValue (retainedWord A 0 m c++[quadraticLetter (j-(((c+1)/2 : Nat) : Int)),shiftLetter a]) x := by
    simpa [FiniteRangeExposure.exposureWord,SourceRangeExpansion.lowerHead,retainedWord,
      List.append_assoc] using hExp.2.2.2
  have hRetainedDom := ((WordAlgebraProof.wordDomain_append (retainedWord A 0 m c)
    [quadraticLetter (j-(((c+1)/2 : Nat) : Int)),shiftLetter a] x).mp hs.1).1
  refine ⟨hOld,hs.2.1,hRetained,hRetainedDom,?_,?_,?_⟩
  · rw [hEq]
    exact hs.2.2.1
  · rw [hEq]
    exact hs.2.2.2.1
  · rw [hEq]
    exact hs.2.2.2.2

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
