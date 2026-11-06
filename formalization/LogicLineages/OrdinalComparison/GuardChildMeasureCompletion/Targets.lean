module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Targets
open PolynomialGraphCompletion

/-- The finite histogram is genuinely well-founded on all literal word pairs. -/
def MeasureWellFounded : Prop := ∀ D, WellFounded (ChildDecrease D)

/-- First E count, then the first differing positive source rank. Higher-rank
counts are unrestricted, so finite mixed-rank expansion is not size descent. -/
def CountCriterion : Prop := ∀ D next current,
  (counterCount next < counterCount current ∨
    (counterCount next = counterCount current ∧ ∃ r,
      1 ≤ r ∧ r ≤ rankBound D ∧ rangeCount r next < rangeCount r current ∧
      ∀ s, 1 ≤ s → s < r → rangeCount s next = rangeCount s current)) →
  ChildDecrease D next current

/-- Swapping the two sides, appending signed outer shifts and normalizing
original outer shifts preserve the measure; these are not recursive decreases. -/
def MeasureInvariance : Prop :=
  (∀ D p, wordMeasure D (p.2,p.1) = wordMeasure D p) ∧
  (∀ D A B j k, wordMeasure D (A++[shiftLetter j],B++[shiftLetter k]) = wordMeasure D (A,B)) ∧
  (∀ D A B, WordAllowed D A → WordAllowed D B →
    wordMeasure D (OuterShiftNormalization.normalizedWord A,OuterShiftNormalization.normalizedWord B) =
      wordMeasure D (A,B))

/-- Every admitted letter rank is covered, including Phi/V at D<2. -/
def AdmissionRankBound : Prop := ∀ D w, WordAllowed D w →
  ∀ a ∈ w, AdjacentRangeWordGuardCompletion.rangeRank a ≤ rankBound D

/-- Checked decrease for every concrete constructor above, including reversed
orientation. No claim is made that a future compiler's entire call graph has
already been constructed or shown to consist of these edges. -/
def ActualGuardChildDecrease : Prop := ∀ D next current,
  GuardChild D next current → ChildDecrease D next current

def ActualGuardChildWellFounded : Prop := ∀ D, WellFounded (GuardChild D)

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Targets
