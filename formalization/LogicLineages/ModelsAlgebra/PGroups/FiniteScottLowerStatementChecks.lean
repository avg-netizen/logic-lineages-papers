module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteScottLower
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.FiniteScottLowerStatementChecks

theorem fixed_nontrivial_no_pi_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupNontrivialNoPiOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.nontrivial_no_pi_one_scott

theorem fixed_finite_no_sigma_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupFiniteNoSigmaOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.finite_no_sigma_one_scott

end LogicLineages.ModelsAlgebra.PGroups.FiniteScottLowerStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
