module

public import LogicLineages.OrdinalComparison.ReserveStageCountProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualReserveIterationGap : LogicLineages.OrdinalComparison.Targets.ActualReserveIterationGap :=
  LogicLineages.OrdinalComparison.actualReserveIterationGap

theorem fixed_actualReserveStageCountLowerBound : LogicLineages.OrdinalComparison.Targets.ActualReserveStageCountLowerBound :=
  LogicLineages.OrdinalComparison.actualReserveStageCountLowerBound

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
