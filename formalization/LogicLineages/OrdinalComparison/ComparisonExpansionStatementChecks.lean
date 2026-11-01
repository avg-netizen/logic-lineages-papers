module
public import LogicLineages.OrdinalComparison.ComparisonExpansionImageProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion.StatementChecks

theorem fixed_image : Targets.ActualComparisonExpansionImage := image
theorem fixed_full : Targets.FullActualComparisonExpansion := full

end LogicLineages.OrdinalComparison.ComparisonExpansion.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonExpansion
