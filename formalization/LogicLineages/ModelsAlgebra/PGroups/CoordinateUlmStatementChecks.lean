module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_pi_finite_ulm : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiFiniteUlm :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_finite_ulm

theorem fixed_finsupp_finite_ulm : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFinsuppFiniteUlm :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finsupp_finite_ulm

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
