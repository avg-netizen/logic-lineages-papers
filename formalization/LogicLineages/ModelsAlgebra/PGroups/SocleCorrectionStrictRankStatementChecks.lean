module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionStrictRank
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_strict_rank : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionStrictRank :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_strict_rank

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
