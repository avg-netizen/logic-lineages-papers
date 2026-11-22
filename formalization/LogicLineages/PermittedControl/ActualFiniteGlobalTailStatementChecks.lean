module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets
import LogicLineages.PermittedControl.ActualFiniteGlobalTailProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualFiniteGlobalTail :
    ActualFiniteGlobalTail.FullActualFiniteGlobalTail :=
  ActualFiniteGlobalTail.fullActualFiniteGlobalTail

#print axioms fixed_actualFiniteGlobalTail

end LogicLineages.PermittedControl.StatementChecks
