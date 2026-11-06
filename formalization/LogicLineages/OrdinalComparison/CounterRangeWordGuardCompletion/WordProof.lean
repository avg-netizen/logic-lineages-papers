module
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.HeadProof
public import LogicLineages.OrdinalComparison.CounterPhiWordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion

theorem counterRangeWordGuardCorrect : Targets.CounterRangeWordGuardCorrect := by
  intro D A B a hA hB ha hr n c j k hn x y hx hy
  have hBx : reachTail B (RangePhiFactorization.factorTail a) ≤ y :=
    (Nat.le_max_right _ _).trans hy
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB hBx
  have hp := rangeHeadPreimage D a (wordValue B y) ha hr hBt.2
  have hP : WordAllowed D (rangeInputWord B a) :=
    RangePhiFactorization.Proof.word_allowed_append D B _ hB hp.1
  have hPD : WordDomain (rangeInputWord B a) y :=
    (WordAlgebraProof.wordDomain_append B _ y).mpr ⟨hBt.1,hp.2.1⟩
  have hfactor : letterValue a (wordValue B y) = Phi (wordValue (rangeInputWord B a) y) := by
    rw [rangeInputWord,WordAlgebraProof.wordValue_append]
    exact hp.2.2.2
  have hs := CounterPhiWordGuardCompletion.Proof.counterPhiWordGuardCorrect D A (rangeInputWord B a)
    hA hP n c j k hn x y ((Nat.le_max_left _ _).trans hx) ((Nat.le_max_left _ _).trans hy)
  rcases hs with ⟨hDL,hDR,hAL,hUL,hlt,heq,hle,hgt⟩
  have hv : wordValue (B++[a,shiftLetter k]) y =
      wordValue (rangeInputWord B a++[phiLetter,shiftLetter k]) y := by
    rw [WordAlgebraProof.wordValue_append,WordAlgebraProof.wordValue_append]
    change wordValue [shiftLetter k] (letterValue a (wordValue B y)) =
      wordValue [shiftLetter k] (Phi (wordValue (rangeInputWord B a) y))
    rw [hfactor]
  have hShift := ((WordAlgebraProof.wordDomain_append (rangeInputWord B a)
    [phiLetter,shiftLetter k] y).mp hDR).2.2.1
  have hRD : WordDomain (B++[a,shiftLetter k]) y := by
    apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    refine ⟨hBt.1,hp.2.2.1,?_,trivial⟩
    change LetterDomain (shiftLetter k) (letterValue a (wordValue B y))
    rw [hfactor]
    exact hShift
  refine ⟨hDL,hRD,hAL,hUL,hP,hPD,?_,?_,?_,?_⟩
  · rw [hv]
    exact hlt
  · rw [hv]
    exact heq
  · rw [hv]
    exact hle
  · rw [hv]
    exact hgt

end LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.Proof
