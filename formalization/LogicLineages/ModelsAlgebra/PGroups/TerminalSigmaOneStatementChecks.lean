module

public import LogicLineages.ModelsAlgebra.PGroups.TerminalSigmaOne
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_terminal_sigma_one_transfer : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTerminalSigmaOneTransfer :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.terminal_sigma_one_transfer

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
