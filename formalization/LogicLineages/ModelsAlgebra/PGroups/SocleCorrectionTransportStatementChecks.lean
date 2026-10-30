module

public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_correction_transport : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionTransport :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_transport

theorem fixed_socle_correction_rank_transport : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleCorrectionRankTransport :=
  LogicLineages.ModelsAlgebra.PGroups.socle_correction_rank_transport

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
