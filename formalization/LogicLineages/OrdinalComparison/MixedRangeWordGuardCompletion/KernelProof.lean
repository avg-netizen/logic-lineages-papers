module
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.FiniteRangeExposure.ContextProof
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem retainedWord_allowed (D : Nat) (A : Word) (n m c : Nat)
    (hA : WordAllowed D A) (hD : n+m+3 ≤ D) : WordAllowed D (retainedWord A n m c) :=
  RangePhiFactorization.Proof.word_allowed_append D A _ hA
    (FiniteRangeExposure.Proof.prefixSyntax D n m c 0 hD).1

theorem shift_allowed (D : Nat) (a : Int) : WordAllowed D [shiftLetter a] := by
  apply RangePhiFactorization.Proof.singleton_allowed
  simp [shiftLetter,LetterAllowed]

theorem mixedKernelGuard : Targets.MixedKernelGuard := by
  intro D A B hA hB n m c e j k a b hD x y hx hy
  have hRetained := retainedWord_allowed D A (n+1) m c hA (by omega)
  have hExp := FiniteRangeExposure.Proof.contextExposure D A [shiftLetter a] (n+1) m c j
    hA (shift_allowed D a) (by omega) x ((Nat.le_max_left _ _).trans hx)
  have hTop : n+1+m+3 = n+m+4 := by omega
  rw [hTop] at hExp
  have hs := ShiftedEqualRankWordGuardCompletion.Proof.shiftedEqualRankWordGuardCorrect D
    (retainedWord A (n+1) m c) B hRetained hB (n+3) c e j k a b (by omega) (by omega) x y
    ((Nat.le_max_right _ _).trans hx) ((Nat.le_max_right _ _).trans hy)
  have hOld : WordDomain (A++[kernelLetter (n+m+4) c j,shiftLetter a]) x := by
    simpa [List.append_assoc] using hExp.2.1
  have hEq : wordValue (A++[kernelLetter (n+m+4) c j,shiftLetter a]) x =
      wordValue (retainedWord A (n+1) m c++[kernelLetter (n+3) c j,shiftLetter a]) x := by
    simpa [FiniteRangeExposure.exposureWord,SourceRangeExpansion.lowerHead,retainedWord,
      List.append_assoc,Nat.add_assoc] using hExp.2.2.2
  have hRetainedDom := ((WordAlgebraProof.wordDomain_append (retainedWord A (n+1) m c)
    [kernelLetter (n+3) c j,shiftLetter a] x).mp hs.1).1
  refine ⟨hOld,hs.2.1,hRetained,hRetainedDom,?_,?_,?_⟩
  · rw [hEq]
    exact hs.2.2.1
  · rw [hEq]
    exact hs.2.2.2.1
  · rw [hEq]
    exact hs.2.2.2.2

end LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.Proof
