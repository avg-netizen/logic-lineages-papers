module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.KeyTargets
/-- The ACTUAL entire-basis balanced-L window forces heterogeneous values,
endpoints and predecessor indices to have the original head-then-COMPLETE-input
ordering. Equality is actual ordinal-head/input equality. No endpoint/order
supplier field or independently ranging head value is assumed. -/
def ActualKeyWindow:Prop:=∀basis:List Nat,∀row:Row,wellFormed basis row→genuineHeads row→
  (∀a∈row.atoms,threshold row ≤ input basis a.2)→
  ∀selected∈row.atoms,(∀a∈row.atoms,input basis selected.2 ≤ input basis a.2)→
  ∀a∈row.atoms,∀b∈row.atoms,
    (atomValue basis a.2 < atomValue basis b.2↔keyLess basis a.2 b.2)∧
    (atomEndpoint basis a.2 < atomEndpoint basis b.2↔keyLess basis a.2 b.2)∧
    (atomIndex basis a.2 < atomIndex basis b.2↔keyLess basis a.2 b.2)∧
    (atomIndex basis a.2=atomIndex basis b.2↔keyEqual basis a.2 b.2)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.KeyTargets
