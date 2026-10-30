module

public import LogicLineages.ModelsAlgebra.PGroups.UlmBasisLift
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_ulm_basis_lift_existence : LogicLineages.ModelsAlgebra.PGroups.Targets.groupUlmBasisLiftExistence :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.ulm_basis_lift_existence

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
