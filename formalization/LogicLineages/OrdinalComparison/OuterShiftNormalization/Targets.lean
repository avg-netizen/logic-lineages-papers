module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion
open AdjacentRangeWordGuardCompletion TerminalWordGrowthCompletion

def SplitSyntax : Prop := ∀ w,
  w = coreWord w ++ shiftSuffix w ∧ ShiftOnly (shiftSuffix w) ∧
  (coreWord w = [] ∨ ∃ A a, coreWord w = A++[a] ∧ a.1 ≠ 0) ∧
  (coreWord w = [] ↔ ShiftOnly w)

/-- Normalization retains all nonlinear occurrences. Rank zero is deliberately
excluded, because it counts shifts rather than source range occurrences. -/
def NormalizationSyntax : Prop := ∀ D w, WordAllowed D w →
  WordAllowed D (coreWord w) ∧ WordAllowed D (shiftSuffix w) ∧
  WordAllowed D (normalizedWord w) ∧
  counterNodes (normalizedWord w) = counterNodes w ∧
  ∀ r, rangeNodes (r+1) (normalizedWord w) = rangeNodes (r+1) w

/-- No intermediate truncation is silently discarded: all original shift
occurrences must have their actual nonnegative input-plus-index domains. -/
def ShiftSumCorrect : Prop := ∀ w t, ShiftOnly w → WordDomain w t →
  (wordValue w t : Int) = (t : Int)+shiftSum w

/-- Original domains imply normalized domains, not conversely. Intermediate
negative shifts can fail even when the final summed shift is nonnegative. -/
def NormalizationCorrect : Prop := ∀ w t, WordDomain w t →
  WordDomain (coreWord w) t ∧ WordDomain (normalizedWord w) t ∧
  wordValue w t = wordValue (normalizedWord w) t ∧
  (wordValue w t : Int) = (wordValue (coreWord w) t : Int)+outerShift w

def TailNormalization : Prop := ∀ D w t, WordAllowed D w → wordTail w ≤ t →
  WordDomain w t ∧ WordDomain (normalizedWord w) t ∧
  wordValue w t = wordValue (normalizedWord w) t

/-- Both raw variables occur only linearly; x=y is permitted and then the
three outcomes reduce to the two fixed integer sums. -/
def LeafComparisons : Prop := ∀ A B x y, ShiftOnly A → ShiftOnly B →
  leafPairTail A B ≤ x → leafPairTail A B ≤ y →
  WordDomain A x ∧ WordDomain B y ∧
  (wordValue A x < wordValue B y ↔ (x : Int)+shiftSum A < (y : Int)+shiftSum B) ∧
  (wordValue A x = wordValue B y ↔ (x : Int)+shiftSum A = (y : Int)+shiftSum B) ∧
  (wordValue A x ≤ wordValue B y ↔ (x : Int)+shiftSum A ≤ (y : Int)+shiftSum B)

/-- The nonlinear/leaf terminal case for an arbitrary original all-shift word
on the smaller input, including the empty word and the same-variable case. -/
def NonlinearLeafGuard : Prop := ∀ D w B x y, WordAllowed D w → Nonlinear w →
  ShiftOnly B → nonlinearLeafTail w B ≤ x → nonlinearLeafTail w B ≤ y → y ≤ x →
  WordDomain w x ∧ WordDomain B y ∧ wordValue B y < wordValue w x

def NormalizationPrograms : Prop := Primrec splitWord ∧ Primrec coreWord ∧
  Primrec shiftSuffix ∧ Primrec shiftSum ∧ Primrec outerShift ∧ Primrec normalizedWord ∧
  Primrec (fun p : Word × Word => leafPairTail p.1 p.2) ∧
  Primrec (fun p : Word × Word => nonlinearLeafTail p.1 p.2)

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets
