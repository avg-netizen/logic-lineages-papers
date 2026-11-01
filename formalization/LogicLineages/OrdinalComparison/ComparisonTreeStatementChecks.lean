module
public import LogicLineages.OrdinalComparison.ComparisonTreeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

theorem fixed_layers_program : Targets.ActualComparisonTreeLayersProgram := layers_program
theorem fixed_full : Targets.FullActualFiniteComparisonTree := full

end LogicLineages.OrdinalComparison.ComparisonTree.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonTree
