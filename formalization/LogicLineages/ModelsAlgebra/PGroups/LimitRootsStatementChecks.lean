module

public import LogicLineages.ModelsAlgebra.PGroups.LimitRoots
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.LimitRootsStatementChecks

theorem fixed_limit_annihilation : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitAnnihilation :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_annihilation

theorem fixed_limit_socle_roots : LogicLineages.ModelsAlgebra.PGroups.Targets.groupLimitSocleRoots :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.limit_socle_roots

end LogicLineages.ModelsAlgebra.PGroups.LimitRootsStatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
