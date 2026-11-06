module
public import LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.SourceRangeExpansion.ContextProof
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem innerWord_allowed (D : Nat) (A : Word) (n c : Nat)
    (hA : WordAllowed D A) (hD : n+3 ≤ D) : WordAllowed D (innerWord A n c) := by
  apply RangePhiFactorization.Proof.word_allowed_append D A _ hA
  apply RangePhiFactorization.Proof.singleton_allowed
  simp [kernelLetter,LetterAllowed,hD]

theorem shift_allowed (D : Nat) (a : Int) : WordAllowed D [shiftLetter a] := by
  apply RangePhiFactorization.Proof.singleton_allowed
  simp [shiftLetter,LetterAllowed]

theorem adjacentKernelGuard : Targets.AdjacentKernelGuard := by
  intro D A B hA hB n c e j k a b hD x y hx hy
  have hInner := innerWord_allowed D A (n+1) c hA (by omega)
  have hExp := SourceRangeExpansion.Proof.contextExpansion D A [shiftLetter a] (n+1) c j
    hA (shift_allowed D a) (by omega) x ((Nat.le_max_left _ _).trans hx)
  have hs := ShiftedEqualRankWordGuardCompletion.Proof.shiftedEqualRankWordGuardCorrect D
    (innerWord A (n+1) c) B hInner hB (n+3) c e j k a b (by omega) (by omega) x y
    ((Nat.le_max_right _ _).trans hx) ((Nat.le_max_right _ _).trans hy)
  have hOld : WordDomain (A++[kernelLetter (n+4) c j,shiftLetter a]) x := by
    simpa [List.append_assoc,Nat.add_assoc] using hExp.2.1
  have hEq : wordValue (A++[kernelLetter (n+4) c j,shiftLetter a]) x =
      wordValue (innerWord A (n+1) c++[kernelLetter (n+3) c j,shiftLetter a]) x := by
    simpa [SourceRangeExpansion.expansionWord,SourceRangeExpansion.lowerHead,innerWord,
      List.append_assoc,Nat.add_assoc] using hExp.2.2.2
  have hInnerDom := ((WordAlgebraProof.wordDomain_append (innerWord A (n+1) c)
    [kernelLetter (n+3) c j,shiftLetter a] x).mp hs.1).1
  refine ⟨hOld,hs.2.1,hInner,hInnerDom,?_,?_,?_⟩
  · rw [hEq]
    exact hs.2.2.1
  · rw [hEq]
    exact hs.2.2.2.1
  · rw [hEq]
    exact hs.2.2.2.2

end LogicLineages.OrdinalComparison.AdjacentRangeWordGuardCompletion.Proof
