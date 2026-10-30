module

public import LogicLineages.OrdinalComparison.PositiveNormalFlagProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_positiveNormalFlagComputable : LogicLineages.OrdinalComparison.Targets.PositiveNormalFlagComputable :=
  LogicLineages.OrdinalComparison.positiveNormalFlagComputable

theorem fixed_positiveNormalFlagCorrect : LogicLineages.OrdinalComparison.Targets.PositiveNormalFlagCorrect :=
  LogicLineages.OrdinalComparison.positiveNormalFlagCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
