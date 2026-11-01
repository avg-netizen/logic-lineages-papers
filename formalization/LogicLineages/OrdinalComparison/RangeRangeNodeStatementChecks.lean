module
public import LogicLineages.OrdinalComparison.RangeRangeNodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode.StatementChecks

theorem fixed_correct : Targets.ActualRangeRangeQueryNodeCorrect := correct
theorem fixed_full : Targets.FullActualRangeRangeQueryNode := full

#print axioms fixed_correct
#print axioms fixed_full

end LogicLineages.OrdinalComparison.RangeRangeNode.StatementChecks
