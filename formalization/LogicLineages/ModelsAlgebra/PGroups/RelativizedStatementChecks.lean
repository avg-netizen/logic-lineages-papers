module

public import LogicLineages.ModelsAlgebra.PGroups.Relativized
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_relativized_top_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRelativizedTopAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.relativized_top_agreement

theorem fixed_relativized_subgroup_agreement : LogicLineages.ModelsAlgebra.PGroups.Targets.groupRelativizedSubgroupAgreement :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.relativized_subgroup_agreement

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
