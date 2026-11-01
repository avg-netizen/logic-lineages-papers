module
public import LogicLineages.OrdinalComparison.ComparisonNodePositiveProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode.StatementChecks

theorem fixed_positive_correct : Targets.ActualPositiveQueryNodeCorrect := positive_correct
theorem fixed_full_positive_node : Targets.FullActualPositiveQueryNode := full_positive_node

end LogicLineages.OrdinalComparison.ComparisonNode.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ComparisonNode
