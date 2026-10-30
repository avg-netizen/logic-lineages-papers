module
public import LogicLineages.OrdinalComparison.OptimizedAlgorithmFuelProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_optimizedMaximumFuelCorrect : Targets.OptimizedMaximumFuelCorrect :=
  optimizedMaximumFuelCorrect

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
