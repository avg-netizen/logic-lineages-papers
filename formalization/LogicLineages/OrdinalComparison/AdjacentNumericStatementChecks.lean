module

public import LogicLineages.OrdinalComparison.AdjacentNumericProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdjacentNumericalGap : LogicLineages.OrdinalComparison.Targets.ActualAdjacentNumericalGap :=
  LogicLineages.OrdinalComparison.actualAdjacentNumericalGap

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
