module
public import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.ScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

private theorem shifted_value (A : Word) (d c x : Nat) (j a : Int)
    (hpos : 0 ≤ (sourceSignedValue d c j (wordValue A x) : Int)+a) :
    (wordValue (A++[kernelLetter d c j,shiftLetter a]) x : Int) =
      (sourceSignedValue d c j (wordValue A x) : Int)+a := by
  rw [WordAlgebraProof.wordValue_append]
  change (((sourceSignedValue d c j (wordValue A x) : Int)+a).toNat : Int) = _
  exact Int.toNat_of_nonneg hpos

theorem shiftedEqualRankWordGuardCorrect : Targets.ShiftedEqualRankWordGuardCorrect := by
  intro D A B hA hB d c e j k a b hd _hD x y hx hy
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA
    ((Nat.le_max_left _ _).trans hx)
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB
    ((Nat.le_max_right _ _).trans hy)
  have hs := shiftedKernelOrder d c e j k a b hd (wordValue A x) (wordValue B y) hAt.2 hBt.2
  have hvL := shifted_value A d c x j a hs.2.2.1.le
  have hvR := shifted_value B d e y k b hs.2.2.2.1.le
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply (WordAlgebraProof.wordDomain_append A _ x).mpr
    exact ⟨hAt.1,hs.1,hs.2.2.1.le,trivial⟩
  · apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    exact ⟨hBt.1,hs.2.1,hs.2.2.2.1.le,trivial⟩
  · have h := hs.2.2.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2.2.2
    rw [←hvL,←hvR] at h
    exact_mod_cast h

theorem headDecrease : Targets.HeadDecrease := by
  intro A B d c e j k
  simp [counterNodes,kernelNodesAt,List.filter_append,kernelLetter]
  omega

end LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.Proof
