module
public import LogicLineages.OrdinalComparison.CounterFixedShiftComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Targets
open CounterLeaderExpansion

/-- Arbitrary actual input pairs, not just a constructed aligned family: every
strict counter gap exceeds K on the explicit pair-dependent quantitative tails. -/
def ActualQuantitativeCounterGap : Prop := ∀ n m c e K t u : Nat,
  CounterFixedShiftComparison.threshold n c e K ≤ t →
  CounterFixedShiftComparison.threshold m e c K ≤ u →
  count (n+3) c t < count (m+3) e u →
  (K : Int) < (count (m+3) e u : Int) - (count (n+3) c t : Int)

/-- True integer shifts of original actual counts. Equal counts compare their
shifts; positivity is derived rather than obtained by natural truncation. -/
def ActualFixedShiftComparison : Prop := ∀ n m c e t u : Nat, ∀ j l : Int,
  CounterFixedShiftComparison.threshold n c e (j.natAbs+l.natAbs) ≤ t →
  CounterFixedShiftComparison.threshold m e c (j.natAbs+l.natAbs) ≤ u →
  0 < (count (n+3) c t : Int)+j ∧
  0 < (count (m+3) e u : Int)+l ∧
  (((count (n+3) c t : Int)+j < (count (m+3) e u : Int)+l) ↔
    count (n+3) c t < count (m+3) e u ∨ (count (n+3) c t = count (m+3) e u ∧ j < l)) ∧
  (((count (n+3) c t : Int)+j = (count (m+3) e u : Int)+l) ↔
    count (n+3) c t = count (m+3) e u ∧ j = l)

end LogicLineages.OrdinalComparison.CounterFixedShiftComparison.Targets
