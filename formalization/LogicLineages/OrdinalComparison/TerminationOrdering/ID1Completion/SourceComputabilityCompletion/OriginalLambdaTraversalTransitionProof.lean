module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBranchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTransitionProof
open OriginalLambdaTraversal OriginalLambdaTraversalStateEvaluationProof
open OriginalLambdaTraversalBranchEvaluationProof
open OriginalHereditaryValidityEvaluationSupportProof (exactOneEvaluation)
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation)
open InternalApplicationResultStackEvaluationProof
  (statusEvaluation workEvaluation resultsEvaluation currentFrameEvaluation restEvaluation
    frameTagEvaluation tailOfEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native calibration is independent of source semantics: all raw status,
frame-tag and underflow branches are checked, including malformed lambdas. -/
theorem actualOriginalLambdaTraversalTransitionCalibration :
    OriginalLambdaTraversalTargets.ActualOriginalLambdaTraversalTransitionCalibration := by
  intro leaf state
  simp only [transition, evalBranch, exactOneEvaluation, sameEvaluation,
    oneEvaluation, twoEvaluation, zeroEvaluation, statusEvaluation,
    applicationExpandedEvaluation, lambdaExpandedEvaluation, leafReturnedEvaluation,
    applicationReturnedEvaluation, lambdaReturnedEvaluation, currentTagEvaluation,
    currentRawEvaluation, currentParameterEvaluation, framePayloadEvaluation,
    frameTagEvaluation, currentFrameEvaluation, restEvaluation, workEvaluation,
    resultsEvaluation, tailOfEvaluation, projectionEvaluation,
    List.Vector.get_ofFn, Matrix.cons_val_zero]
  unfold transitionValue
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTransitionProof
