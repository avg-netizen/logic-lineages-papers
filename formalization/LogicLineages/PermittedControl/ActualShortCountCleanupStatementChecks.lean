module
public import LogicLineages.PermittedControl.ActualShortCountCleanupTargets
import LogicLineages.PermittedControl.ActualShortCountCleanupProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualShortCountCleanup :
    ActualShortCountCleanup.FullActualShortCountCleanup :=
  ActualShortCountCleanup.fullActualShortCountCleanup

#print axioms fixed_actualShortCountCleanup

end LogicLineages.PermittedControl.StatementChecks
