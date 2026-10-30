module

public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLower
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_raw_finite_no_sigma_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawFiniteNoSigmaOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_finite_no_sigma_one_scott

theorem fixed_raw_nontrivial_no_pi_one_scott : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRawNontrivialNoPiOneScott :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.raw_nontrivial_no_pi_one_scott

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
