module

public import LogicLineages.OrdinalComparison.ReserveStageInputProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualReserveStageDomain : LogicLineages.OrdinalComparison.Targets.ActualReserveStageDomain :=
  LogicLineages.OrdinalComparison.actualReserveStageDomain

theorem fixed_actualReserveStageFirstResidual : LogicLineages.OrdinalComparison.Targets.ActualReserveStageFirstResidual :=
  LogicLineages.OrdinalComparison.actualReserveStageFirstResidual

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
