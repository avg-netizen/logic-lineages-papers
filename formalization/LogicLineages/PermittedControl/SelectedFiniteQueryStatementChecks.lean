module
public import LogicLineages.PermittedControl.SelectedFiniteQueryProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_selectedFiniteQuery : SelectedFiniteQueryTargets.SelectedFiniteQuery :=
  SelectedFiniteQuery.Proof.selectedFiniteQuery
#print axioms fixed_selectedFiniteQuery
end LogicLineages.PermittedControl.StatementChecks
