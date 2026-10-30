module

public import LogicLineages.OrdinalComparison.LinkedTransientProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualBinaryPoleBudgetQuadratic : LogicLineages.OrdinalComparison.Targets.ActualBinaryPoleBudgetQuadratic :=
  LogicLineages.OrdinalComparison.actualBinaryPoleBudgetQuadratic

theorem fixed_actualLinkedPoleTransient : LogicLineages.OrdinalComparison.Targets.ActualLinkedPoleTransient :=
  LogicLineages.OrdinalComparison.actualLinkedPoleTransient

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
