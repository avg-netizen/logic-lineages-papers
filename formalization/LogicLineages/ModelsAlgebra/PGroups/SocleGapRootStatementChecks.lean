module

public import LogicLineages.ModelsAlgebra.PGroups.SocleGapRoot
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_gap_suitable_root : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleGapSuitableRoot :=
  LogicLineages.ModelsAlgebra.PGroups.socle_gap_suitable_root

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
