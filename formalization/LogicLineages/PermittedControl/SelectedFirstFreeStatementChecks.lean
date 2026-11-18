module
public import LogicLineages.PermittedControl.SelectedFirstFreeProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_fullSelectedFirstFree : SelectedFirstFreeTargets.FullSelectedFirstFree :=
  SelectedFirstFreeProof.fullSelectedFirstFree
#print axioms fixed_fullSelectedFirstFree

end LogicLineages.PermittedControl.StatementChecks
