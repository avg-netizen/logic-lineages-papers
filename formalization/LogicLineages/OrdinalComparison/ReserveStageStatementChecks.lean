module

public import LogicLineages.OrdinalComparison.ReserveStageProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_fullActualOneStageReserve : LogicLineages.OrdinalComparison.Targets.FullActualOneStageReserve :=
  LogicLineages.OrdinalComparison.fullActualOneStageReserve

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
