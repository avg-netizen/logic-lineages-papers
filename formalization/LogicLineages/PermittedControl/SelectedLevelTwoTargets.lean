module
public import LogicLineages.PermittedControl.SelectedFiniteQueryTargets
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedLevelTwoTargets
open OrdinalComparison Source
open Source.AdmissibleSum

/-- Complete printed finite-query level-two clause, not the additional level-three clause. -/
def SelectedLevelTwo : Prop := ∀ ctrl K, SelectedWithThreshold ctrl K → ∀ policy : Policy,
  SelectedFiniteQuery.FiniteQueryReduction ctrl policy true ∧
  SelectedFiniteQuery.FiniteQueryReduction ctrl policy false ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 2 true) ∧
  (¬SelectedFiniteQuery.HasComparisonDecider ctrl policy 2 false)
end LogicLineages.PermittedControl.SelectedLevelTwoTargets
