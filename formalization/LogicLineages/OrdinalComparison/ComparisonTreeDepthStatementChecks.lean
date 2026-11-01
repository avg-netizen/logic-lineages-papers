module
public import LogicLineages.OrdinalComparison.ComparisonTreeDepthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

theorem fixed_depth_program : Targets.ActualComparisonDepthProgram := depth_program

end LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonTree
