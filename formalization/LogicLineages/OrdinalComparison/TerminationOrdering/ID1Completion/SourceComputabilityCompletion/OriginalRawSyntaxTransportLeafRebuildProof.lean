module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportLeafRebuildProof
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem leafEvaluation (mode : Mode) (v : List.Vector Nat 3) :
    evaluate (leaf mode) v = leafValue mode (v.get 0) (v.get 1) (v.get 2) := by
  cases mode <;>
    simp only [leaf, evalBranch, sameOfEvaluation, lessCompositionEvaluation,
      predecessorCompositionEvaluation, pairOfEvaluation, leftOfEvaluation,
      rightOfEvaluation, constantEvaluation, succOfEvaluation,
      projectionEvaluation, leafValue, tagValue, payloadValue] <;>
    split_ifs <;> simp_all

 theorem rebuildEvaluation (mode : Mode) (v : List.Vector Nat 3) :
    evaluate (rebuild mode) v = rebuildValue mode (v.get 0) (v.get 1) (v.get 2) := by
  cases mode <;>
    simp only [rebuild, evalBranch, sameOfEvaluation, arityOfEvaluation,
      pairOfEvaluation, leftOfEvaluation, rightOfEvaluation, constantEvaluation,
      addOfEvaluation, projectionEvaluation, rebuildValue, tagValue, payloadValue] <;>
    split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportLeafRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportLeafRebuildProof
