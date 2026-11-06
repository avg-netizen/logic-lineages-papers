module
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.ScalarProof
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.HeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterRangeWordGuardCompletion CounterWordGuardCompletion

theorem phiRangeWordGuardCorrect : Targets.PhiRangeWordGuardCorrect := by
  intro D A B a hA hB ha hr j k x y hx hy
  have hAx : reachTail A (scalarTail j k) ≤ x := (Nat.le_max_left _ _).trans hx
  have hBx : reachTail B (RangePhiFactorization.factorTail a) ≤ y :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hy)
  have hPx : reachTail (rangeInputWord B a) (scalarTail j k) ≤ y :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hy)
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA hAx
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB hBx
  have hp := CounterRangeWordGuardCompletion.Proof.rangeHeadPreimage D a (wordValue B y) ha hr hBt.2
  have hP : WordAllowed D (rangeInputWord B a) :=
    RangePhiFactorization.Proof.word_allowed_append D B _ hB hp.1
  have hPt := WordGuardCompletion.Proof.wordReachCorrect D (rangeInputWord B a) _ y hP hPx
  have hfactor : letterValue a (wordValue B y) = Phi (wordValue (rangeInputWord B a) y) := by
    rw [rangeInputWord,WordAlgebraProof.wordValue_append]
    exact hp.2.2.2
  have hs := shiftedPhiOrder j k (wordValue A x) (wordValue (rangeInputWord B a) y) hAt.2 hPt.2
  have hvL : (wordValue (A++[phiLetter,shiftLetter j]) x : Int) =
      (Phi (wordValue A x) : Int)+j := by
    rw [WordAlgebraProof.wordValue_append]
    change (((Phi (wordValue A x) : Int)+j).toNat : Int) = _
    exact Int.toNat_of_nonneg hs.1.le
  have hvR : (wordValue (B++[a,shiftLetter k]) y : Int) =
      (Phi (wordValue (rangeInputWord B a) y) : Int)+k := by
    rw [WordAlgebraProof.wordValue_append]
    change (((letterValue a (wordValue B y) : Int)+k).toNat : Int) = _
    rw [hfactor]
    exact Int.toNat_of_nonneg hs.2.1.le
  refine ⟨?_,?_,hP,hPt.1,?_,?_,?_⟩
  · apply (WordAlgebraProof.wordDomain_append A _ x).mpr
    exact ⟨hAt.1,trivial,hs.1.le,trivial⟩
  · apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    refine ⟨hBt.1,hp.2.2.1,?_,trivial⟩
    change 0 ≤ (letterValue a (wordValue B y) : Int)+k
    rw [hfactor]
    exact hs.2.1.le
  · have h := hs.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2
    rw [←hvL,←hvR] at h
    exact_mod_cast h

theorem headDecrease : Targets.HeadDecrease := by
  intro A B a hr
  rcases hr with h | h | h <;>
    simp [rangeInputWord,preimageWord,RangePhiFactorization.predecessorHead,
      counterNodes,phiNodes,List.filter_append,phiLetter,h] <;> omega

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof
