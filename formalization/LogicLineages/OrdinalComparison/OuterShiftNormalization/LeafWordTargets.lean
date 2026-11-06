module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets
open PolynomialGraphCompletion

/-- Exact terminal leaf/word scalar view: the first raw argument occurs only
linearly. This identity alone is not a same-variable decision algorithm;
when raw variable names coincide, use leaf sums or nonlinear growth instead. -/
def LeafWordComparisons : Prop := ∀ D A B x y, ShiftOnly A → WordAllowed D B →
  leafPairTail A B ≤ x → leafPairTail A B ≤ y →
  WordDomain A x ∧ WordDomain B y ∧
  (wordValue A x < wordValue B y ↔ (x : Int)+shiftSum A < (wordValue B y : Int)) ∧
  (wordValue A x = wordValue B y ↔ (x : Int)+shiftSum A = (wordValue B y : Int)) ∧
  (wordValue A x ≤ wordValue B y ↔ (x : Int)+shiftSum A ≤ (wordValue B y : Int))

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets
