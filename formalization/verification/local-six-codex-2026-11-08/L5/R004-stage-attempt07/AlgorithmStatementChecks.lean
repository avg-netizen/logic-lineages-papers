module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks

theorem intrinsic_stage_syntax_and_decrease : AlgorithmTargets.IntrinsicStageSyntaxAndDecrease :=
  AlgorithmProof.intrinsicStageSyntaxAndDecrease

theorem exact_stage_semantics : AlgorithmTargets.ExactStageSemantics :=
  AlgorithmProof.exactStageSemantics

theorem actual_stage_program : AlgorithmTargets.ActualStageProgram :=
  AlgorithmPrograms.actualStageProgram

theorem exact_finite_ranked_stage : AlgorithmTargets.ExactFiniteRankedStage :=
  AlgorithmProof.exactFiniteRankedStage

#print axioms intrinsic_stage_syntax_and_decrease
#print axioms exact_stage_semantics
#print axioms actual_stage_program
#print axioms exact_finite_ranked_stage

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks
