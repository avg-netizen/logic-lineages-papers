module

public import LogicLineages.ModelsAlgebra.PGroups.TerminalLayer
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_internal_sum_quotient_image : LogicLineages.ModelsAlgebra.PGroups.Targets.groupInternalSumQuotientImage :=
  LogicLineages.ModelsAlgebra.PGroups.internal_sum_quotient_image

theorem fixed_terminal_layer_quotient : LogicLineages.ModelsAlgebra.PGroups.Targets.groupTerminalLayerQuotient :=
  LogicLineages.ModelsAlgebra.PGroups.terminal_layer_quotient

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
