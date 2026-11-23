module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionTargets
public import LogicLineages.PermittedControl.GroundComparisonMainTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PolicyIndexedMainComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open StandardControlCurrent.PolicyIndexedShape (EveryEffectivePolicyHasIndex)
open PolicyIndexedGroundDriver (IndexedGroundDecidable)

def IndexedGroundBothControls : Prop :=
  IndexedGroundDecidable factorialControl ∧ ∀ b : Nat, IndexedGroundDecidable (nearControl b)

/-- The same original comparison classification as the ground and hardness
comparators, strengthening the positive clause to actual policy-code
specialization and recording that every effective selector has an index.
The near-control parameter is still quantified as a fixed control. -/
def IndexedMainComparison : Prop :=
  Targets.FullControl ∧ Targets.NearControlModular ∧ EveryEffectivePolicyHasIndex ∧
    IndexedGroundBothControls ∧ SelectedFunctionalHardnessTargets.SelectedFunctionalHardness

end LogicLineages.PermittedControl.PolicyIndexedMainComparison
