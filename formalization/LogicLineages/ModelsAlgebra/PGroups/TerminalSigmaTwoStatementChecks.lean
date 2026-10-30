module

public import LogicLineages.ModelsAlgebra.PGroups.TerminalSigmaTwo
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_terminal_sigma_two_transfer : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTerminalSigmaTwoTransfer :=
  LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary.terminal_sigma_two_transfer

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
