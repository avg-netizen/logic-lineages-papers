module
public import LogicLineages.OrdinalComparison.RangePositiveNodeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode.StatementChecks

theorem fixed_range_correct : Targets.ActualRangePositiveQueryNodeCorrect := range_correct
theorem fixed_positive_range_correct : Targets.ActualPositiveRangeQueryNodeCorrect := positive_range_correct
theorem fixed_full : Targets.FullActualRangePositiveQueryNode := full

end LogicLineages.OrdinalComparison.RangePositiveNode.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.RangePositiveNode
