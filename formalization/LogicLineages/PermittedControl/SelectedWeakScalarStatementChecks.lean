module
public import LogicLineages.PermittedControl.SelectedWeakScalarProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_fullSelectedWeakScalar : SelectedWeakScalarTargets.FullSelectedWeakScalar :=
  SelectedWeakScalarProof.fullSelectedWeakScalar
#print axioms fixed_fullSelectedWeakScalar

end LogicLineages.PermittedControl.StatementChecks
