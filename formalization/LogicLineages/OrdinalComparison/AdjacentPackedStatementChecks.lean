module

public import LogicLineages.OrdinalComparison.AdjacentPackedProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdjacentLeadingCoverage : LogicLineages.OrdinalComparison.Targets.ActualAdjacentLeadingCoverage :=
  LogicLineages.OrdinalComparison.actualAdjacentLeadingCoverage

theorem fixed_actualAdjacentPackedState : LogicLineages.OrdinalComparison.Targets.ActualAdjacentPackedState :=
  LogicLineages.OrdinalComparison.actualAdjacentPackedState

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
