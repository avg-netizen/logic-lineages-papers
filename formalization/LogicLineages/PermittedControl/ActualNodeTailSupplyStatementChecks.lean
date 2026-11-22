module
public import LogicLineages.PermittedControl.ActualNodeTailSupplyTargets
import LogicLineages.PermittedControl.ActualNodeTailSupplyProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_actualNodeTailSupply :
    ActualNodeTailSupply.FullActualNodeTailSupply :=
  ActualNodeTailSupply.fullActualNodeTailSupply

#print axioms fixed_actualNodeTailSupply

end LogicLineages.PermittedControl.StatementChecks
