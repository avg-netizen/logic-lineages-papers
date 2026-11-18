module
public import LogicLineages.PermittedControl.SelectedLevelTwoTargets
public import LogicLineages.PermittedControl.SelectedSingleQueryTargets
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalHardnessTargets
open OrdinalComparison Source Source.AdmissibleSum

/-- Complete current theorem: both relations, actual unrestricted printed domains,
finite-query level two and one-query level three, uniformly over selected controls/policies. -/
def SelectedFunctionalHardness : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K →
  ∀ policy : Policy,
  SelectedFiniteQuery.FiniteQueryReduction ctrl policy true ∧
  SelectedFiniteQuery.FiniteQueryReduction ctrl policy false ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 2 true) ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 2 false) ∧
  SelectedSingleQuery.SingleQueryReduction ctrl policy true ∧
  SelectedSingleQuery.SingleQueryReduction ctrl policy false ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 3 true) ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 3 false)
end LogicLineages.PermittedControl.SelectedFunctionalHardnessTargets
