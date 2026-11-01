module
public import LogicLineages.OrdinalComparison.SingleCoreEvaluationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreEvaluation.StatementChecks

theorem fixed_code : Targets.ActualSingleCoreGroundCode := source_code
theorem fixed_value : Targets.ActualSingleCoreGroundValue := source_value
theorem fixed_full : Targets.FullActualSingleCoreEvaluation := full

#print axioms fixed_code
#print axioms fixed_value
#print axioms fixed_full

end LogicLineages.OrdinalComparison.SingleCoreEvaluation.StatementChecks
