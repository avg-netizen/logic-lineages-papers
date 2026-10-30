module

public import LogicLineages.OrdinalComparison.HahnSquareProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualHahnSquareEvenCoefficient : LogicLineages.OrdinalComparison.Targets.ActualHahnSquareEvenCoefficient :=
  LogicLineages.OrdinalComparison.actualHahnSquareEvenCoefficient

theorem fixed_actualHahnSquareOddCoefficient : LogicLineages.OrdinalComparison.Targets.ActualHahnSquareOddCoefficient :=
  LogicLineages.OrdinalComparison.actualHahnSquareOddCoefficient

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
