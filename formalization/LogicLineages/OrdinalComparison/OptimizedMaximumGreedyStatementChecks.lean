module
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLowerPowerGreedyRecurrence : Targets.ActualLowerPowerGreedyRecurrence :=
  actualLowerPowerGreedyRecurrence

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
