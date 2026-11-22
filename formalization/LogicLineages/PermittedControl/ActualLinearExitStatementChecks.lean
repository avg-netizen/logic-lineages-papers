module
public import LogicLineages.PermittedControl.ActualLinearExitTargets
import LogicLineages.PermittedControl.ActualLinearExitProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualLinearExit : ActualLinearExit.ExactActualLinearExit :=
  ActualLinearExit.exactActualLinearExit

#print axioms fixed_actualLinearExit

end LogicLineages.PermittedControl.StatementChecks
