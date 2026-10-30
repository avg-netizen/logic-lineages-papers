module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_pi_finite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiFiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_finite_filtration

theorem fixed_pi_finite_socle : LogicLineages.ModelsAlgebra.PGroups.Targets.groupPiFiniteSocle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.pi_finite_socle

theorem fixed_finsupp_finite_filtration : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFinsuppFiniteFiltration :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finsupp_finite_filtration

theorem fixed_finsupp_finite_socle : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFinsuppFiniteSocle :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finsupp_finite_socle

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
