module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.DominanceTargets
/-- Actual heterogeneous balanced row AFTER equal-head/COMPLETE-input collection.
The original L, ALL shared basis entries and open outside remainder are kept.
The selected nonzero coefficient is largest by the actual source key, with no
endpoint, index, band, dominance or remainder-size field assumed. Collection
and the all-cancelled lower-layer branch are still separate obligations. -/
def ActualSurvivingDominance:Prop:=∀basis:List Nat,∀row:Row,
  wellFormed basis row→genuineHeads row→
  (row.atoms.Pairwise (fun a b=>¬keyEqual basis a.2 b.2))→
  (∀a∈row.atoms,threshold row ≤ input basis a.2)→
  ∀selected∈row.atoms,(∀a∈row.atoms,input basis selected.2 ≤ input basis a.2)→
  ∀winner∈row.atoms,winner.1≠0→(∀a∈row.atoms,¬keyLess basis winner.2 a.2)→
    Int.sign (value basis row)=Int.sign winner.1
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.DominanceTargets
