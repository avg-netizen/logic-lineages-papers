module
public import LogicLineages.OrdinalComparison.RangeRangeNodeEqualProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode.StatementChecks

theorem fixed_equal_correct : Targets.ActualSameOuterRangeQueryNodeCorrect := equal_correct

end LogicLineages.OrdinalComparison.RangeRangeNode.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.RangeRangeNode
