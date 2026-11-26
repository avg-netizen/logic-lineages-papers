module
public import LogicLineages.PermittedControl.SelectedSingleQueryProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_selectedSingleQuery : SelectedSingleQueryTargets.SelectedSingleQuery :=
  SelectedSingleQuery.Proof.selectedSingleQuery
#print axioms fixed_selectedSingleQuery
end LogicLineages.PermittedControl.StatementChecks
