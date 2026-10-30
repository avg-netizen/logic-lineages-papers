module

public import LogicLineages.OrdinalComparison.PositiveFiniteZerosProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualPositiveFiniteZeros : LogicLineages.OrdinalComparison.Targets.FullActualPositiveFiniteZeros :=
  LogicLineages.OrdinalComparison.fullActualPositiveFiniteZeros

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
