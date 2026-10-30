module

public import LogicLineages.ModelsAlgebra.PGroups.SocleGapExtension
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_socle_gap_preserving_extension : LogicLineages.ModelsAlgebra.PGroups.Targets.groupSocleGapPreservingExtension :=
  LogicLineages.ModelsAlgebra.PGroups.socle_gap_preserving_extension

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
