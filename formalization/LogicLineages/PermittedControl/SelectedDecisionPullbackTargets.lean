module
public import LogicLineages.PermittedControl.SelectedFiniteQueryDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedDecisionPullbackTargets
open OrdinalComparison Source
open Source.AdmissibleSum

/-- Explicit conditional helper, not an undecidability premise or conclusion. -/
def FiniteQueryPullback : Prop := ∀ (ctrl : Nat → Nat) (policy : Policy) (strict : Bool),
  SelectedFiniteQuery.FiniteQueryReduction ctrl policy strict →
  SelectedFiniteQuery.HasComparisonDecider ctrl policy 2 strict →
  ComputablePred FunctionalHardnessCompletion.encodedPolynomialSolvable
end LogicLineages.PermittedControl.SelectedDecisionPullbackTargets
