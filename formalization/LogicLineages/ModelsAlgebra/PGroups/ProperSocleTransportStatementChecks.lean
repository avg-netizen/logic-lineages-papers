module

public import LogicLineages.ModelsAlgebra.PGroups.ProperSocleTransport
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_proper_socle_transport : LogicLineages.ModelsAlgebra.PGroups.Targets.groupProperSocleTransport :=
  LogicLineages.ModelsAlgebra.PGroups.proper_socle_transport

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
