module

public import LogicLineages.ModelsAlgebra.PGroups.CoherentTerminal
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_coherent_terminal_quotient : LogicLineages.ModelsAlgebra.PGroups.Targets.groupCoherentTerminalQuotient :=
  LogicLineages.ModelsAlgebra.PGroups.coherent_terminal_quotient

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
