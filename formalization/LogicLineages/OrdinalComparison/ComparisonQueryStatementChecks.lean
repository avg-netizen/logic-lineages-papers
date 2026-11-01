module
public import LogicLineages.OrdinalComparison.ComparisonQueryProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonQuery.StatementChecks

theorem fixed_coverage : Targets.ActualComparisonQueryRequestCoverage := coverage
theorem fixed_child_projection : Targets.ActualComparisonQueryChildProjection := child_projection
theorem fixed_frontier_projection : Targets.ActualComparisonQueryFrontierProjection := frontier_projection
theorem fixed_layers_program : Targets.ActualComparisonQueryLayersProgram := layers_program
theorem fixed_full : Targets.FullActualFiniteComparisonQueryTree := full

end LogicLineages.OrdinalComparison.ComparisonQuery.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonQuery
