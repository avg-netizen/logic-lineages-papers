module
public import LogicLineages.PermittedControl.SelectedFiniteQueryDefinitions
public import LogicLineages.PermittedControl.SelectedSingleQueryDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalHardness
open OrdinalComparison Source Source.AdmissibleSum

/-- Corollary `cor:standard-functional-hardness`: both relations at the unchanged
displayed control Phi, actual unrestricted printed domains, finite-query internal
level two and single-query internal level three, for every genuine policy. No
selected-control premise, modular potential or count residue occurs. -/
def StandardFunctionalHardness : Prop := ∀ policy : Policy,
  SelectedFiniteQuery.FiniteQueryReduction Phi policy true ∧
  SelectedFiniteQuery.FiniteQueryReduction Phi policy false ∧
  (¬SelectedFiniteQuery.HasComparisonDecider Phi policy 2 true) ∧
  (¬SelectedFiniteQuery.HasComparisonDecider Phi policy 2 false) ∧
  SelectedSingleQuery.SingleQueryReduction Phi policy true ∧
  SelectedSingleQuery.SingleQueryReduction Phi policy false ∧
  (¬SelectedFiniteQuery.HasComparisonDecider Phi policy 3 true) ∧
  (¬SelectedFiniteQuery.HasComparisonDecider Phi policy 3 false)
end LogicLineages.PermittedControl.StandardFunctionalHardness
