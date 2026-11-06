module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.SemanticProof
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.LeafWordTargets
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.TerminalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem leafComparisons : Targets.LeafComparisons := by
  intro A B x y hA hB hx hy
  have hdA := (WordGuardCompletion.Proof.wordTailCorrect 0 A x (shiftOnly_allowed 0 A hA)
    ((Nat.le_max_left _ _).trans hx)).1
  have hdB := (WordGuardCompletion.Proof.wordTailCorrect 0 B y (shiftOnly_allowed 0 B hB)
    ((Nat.le_max_right _ _).trans hy)).1
  have hvA := shiftSumCorrect A x hA hdA
  have hvB := shiftSumCorrect B y hB hdB
  exact ⟨hdA,hdB,by omega,by omega,by omega⟩

theorem leafWordComparisons : Targets.LeafWordComparisons := by
  intro D A B x y hA hB hx hy
  have hdA := (WordGuardCompletion.Proof.wordTailCorrect D A x (shiftOnly_allowed D A hA)
    ((Nat.le_max_left _ _).trans hx)).1
  have hdB := (WordGuardCompletion.Proof.wordTailCorrect D B y hB
    ((Nat.le_max_right _ _).trans hy)).1
  have hvA := shiftSumCorrect A x hA hdA
  exact ⟨hdA,hdB,by omega,by omega,by omega⟩

theorem nonlinearLeafGuard : Targets.NonlinearLeafGuard := by
  intro D w B x y hw hnon hB hx hy hyx
  have hg := TerminalWordGrowthCompletion.Proof.terminalGuard D w x y (shiftSum B) hw hnon
    ((Nat.le_max_left _ _).trans hx) ((Nat.le_max_left _ _).trans hy) hyx
  have hdB := (WordGuardCompletion.Proof.wordTailCorrect D B y (shiftOnly_allowed D B hB)
    ((Nat.le_max_right _ _).trans hy)).1
  have hsum := shiftSumCorrect B y hB hdB
  have hv : wordValue [shiftLetter (shiftSum B)] y = wordValue B y := by
    change ((y : Int)+shiftSum B).toNat = wordValue B y
    omega
  refine ⟨hg.1,hdB,?_⟩
  rw [← hv]
  exact hg.2.2

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
