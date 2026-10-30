module

public import LogicLineages.ModelsAlgebra.PGroups.TerminalExactLength
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_terminal_exact_length : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTerminalExactLength :=
  LogicLineages.ModelsAlgebra.PGroups.terminal_exact_length

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
