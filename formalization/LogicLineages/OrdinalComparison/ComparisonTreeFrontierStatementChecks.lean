module
public import LogicLineages.OrdinalComparison.ComparisonTreeFrontierProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

theorem fixed_frontier_program : Targets.ActualComparisonFrontierProgram := frontier_program
theorem fixed_terminates : Targets.ActualComparisonFrontierTerminates := terminates

end LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonTree
