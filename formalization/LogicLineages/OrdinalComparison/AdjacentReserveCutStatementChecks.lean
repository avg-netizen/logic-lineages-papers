module

public import LogicLineages.OrdinalComparison.AdjacentReserveCutProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualAdjacentReserveCut : LogicLineages.OrdinalComparison.Targets.ActualAdjacentReserveCut :=
  LogicLineages.OrdinalComparison.actualAdjacentReserveCut

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
