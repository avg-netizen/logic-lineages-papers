module

public import LogicLineages.ModelsAlgebra.PGroups.NextBlockUlm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.StatementChecks

theorem fixed_quotient_next_block_ulm_inequality : LogicLineages.ModelsAlgebra.PGroups.Targets.groupQuotientNextBlockUlmInequality :=
  LogicLineages.ModelsAlgebra.PGroups.quotient_next_block_ulm_inequality

end LogicLineages.ModelsAlgebra.PGroups.StatementChecks

#audit_namespace LogicLineages.ModelsAlgebra.PGroups
