module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderBranchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderNumericDispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransitionProof
open OriginalTypedDecoder OriginalTypedDecoderEvaluationSupportProof OriginalTypedDecoderSelectorProof
open OriginalTypedDecoderBranchEvaluationProof OriginalTypedDecoderNumericDispatchProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem termDispatchEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (termDispatch H) v = termResult (programValue H)
      (evaluate gamma v) (evaluate typ v) (evaluate raw v) (evaluate rest v) := by
  simp only [termDispatch, ifSameEvaluation, constantEvaluation, variableStepEvaluation,
    lambdaStepEvaluation, applicationStepEvaluation, bottomStepEvaluation,
    ordinaryStepEvaluation, numberedStepEvaluation, tagEvaluation, payloadEvaluation, termResult]

 theorem argumentsDispatchEvaluation (v : List.Vector Nat 1) :
    evaluate argumentsDispatch v = argumentsResult
      (evaluate gamma v) (evaluate typ v) (evaluate raw v) (evaluate rest v) := by
  simp only [argumentsDispatch, ifSameEvaluation, constantEvaluation,
    nilStepEvaluation, consStepEvaluation, tagEvaluation, payloadEvaluation, argumentsResult]

/-- Small compositional equations avoid expanding the entire nested dispatch
inside a global case split. The frozen transition and its output are unchanged. -/
 theorem transitionEvaluation (H : Program 1) (v : List.Vector Nat 1) :
    evaluate (transition H) v = transitionValue (programValue H) (v.get 0) := by
  simp only [transition, ifSameEvaluation, evalBranch, constantEvaluation, projectionEvaluation,
    termDispatchEvaluation, argumentsDispatchEvaluation, modeEvaluation, gammaEvaluation,
    typEvaluation, rawEvaluation, statusEvaluation, currentRequestEvaluation,
    restEvaluation, workEvaluation, transitionValueEquation, expansionResultEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransitionProof
