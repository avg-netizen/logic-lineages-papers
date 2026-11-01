module
public import LogicLineages.OrdinalComparison.RangePositiveNodeSourceProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode.StatementChecks

theorem fixed_open_growth : Targets.ActualOpenSourceUnconditionalGrowth := open_growth
theorem fixed_range_image : Targets.ActualGenuineRangeSourceImage := range_image

end LogicLineages.OrdinalComparison.RangePositiveNode.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.RangePositiveNode
