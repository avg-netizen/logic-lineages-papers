module

public import LogicLineages.ModelsAlgebra.PGroups.CoprimeFiltration
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_coprime_subgroup_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCoprimeSubgroupMembership :=
  LogicLineages.ModelsAlgebra.PGroups.coprime_subgroup_membership

theorem fixed_coprime_filtration_membership : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCoprimeFiltrationMembership :=
  LogicLineages.ModelsAlgebra.PGroups.coprime_filtration_membership

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
