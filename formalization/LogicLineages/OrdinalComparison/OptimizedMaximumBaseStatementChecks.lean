module
public import LogicLineages.OrdinalComparison.OptimizedMaximumBaseProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOptimizedMaximumBaseCases : Targets.ActualOptimizedMaximumBaseCases :=
  actualOptimizedMaximumBaseCases
theorem fixed_optimizedMaximumCallsDecrease : Targets.OptimizedMaximumCallsDecrease := optimizedMaximumCallsDecrease

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
