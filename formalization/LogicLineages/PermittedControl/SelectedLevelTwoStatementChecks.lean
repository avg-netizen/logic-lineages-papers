module
public import LogicLineages.PermittedControl.SelectedLevelTwoProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_selectedLevelTwo : SelectedLevelTwoTargets.SelectedLevelTwo :=
  SelectedLevelTwo.Proof.selectedLevelTwo
#print axioms fixed_selectedLevelTwo
end LogicLineages.PermittedControl.StatementChecks
