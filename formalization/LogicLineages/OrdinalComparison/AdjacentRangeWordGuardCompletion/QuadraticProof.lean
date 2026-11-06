module
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.KernelProof
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem cubicQuadraticGuard : Targets.CubicQuadraticGuard := by
  intro D A B hA hB c j k a b hD x y hx hy
  have hInner := innerWord_allowed D A 0 c hA hD
  have hExp := SourceRangeExpansion.Proof.contextExpansion D A [shiftLetter a] 0 c j
    hA (shift_allowed D a) hD x ((Nat.le_max_left _ _).trans hx)
  have hs := QuadraticWordGuardCompletion.Proof.quadraticWordGuardCorrect D
    (innerWord A 0 c) B hInner hB (j-(((c+1)/2 : Nat) : Int)) k a b x y
    ((Nat.le_max_right _ _).trans hx) ((Nat.le_max_right _ _).trans hy)
  have hOld : WordDomain (A++[kernelLetter 3 c j,shiftLetter a]) x := by
    simpa [List.append_assoc] using hExp.2.1
  have hEq : wordValue (A++[kernelLetter 3 c j,shiftLetter a]) x =
      wordValue (innerWord A 0 c++[quadraticLetter (j-(((c+1)/2 : Nat) : Int)),shiftLetter a]) x := by
    simpa [SourceRangeExpansion.expansionWord,SourceRangeExpansion.lowerHead,innerWord,
      List.append_assoc] using hExp.2.2.2
  have hInnerDom := ((WordAlgebraProof.wordDomain_append (innerWord A 0 c)
    [quadraticLetter (j-(((c+1)/2 : Nat) : Int)),shiftLetter a] x).mp hs.1).1
  refine ⟨hOld,hs.2.1,hInner,hInnerDom,?_,?_,?_⟩
  · rw [hEq]
    exact hs.2.2.1
  · rw [hEq]
    exact hs.2.2.2.1
  · rw [hEq]
    exact hs.2.2.2.2

end LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
