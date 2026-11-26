module
public import LogicLineages.PermittedControl.SelectedBoxHeadProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_fullSelectedBox : SelectedBoxTargets.FullSelectedBox :=
  SelectedBoxHeadProof.fullSelectedBox
#print axioms fixed_fullSelectedBox

end LogicLineages.PermittedControl.StatementChecks
