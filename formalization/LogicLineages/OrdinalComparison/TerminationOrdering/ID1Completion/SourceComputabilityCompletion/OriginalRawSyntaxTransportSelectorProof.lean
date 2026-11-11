module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem rawTagEvaluation (v : List.Vector Nat 1) :
    evaluate rawTag v = tagValue (v.get 0) := leftEvaluation v

 theorem rawPayloadEvaluation (v : List.Vector Nat 1) :
    evaluate rawPayload v = payloadValue (v.get 0) := rightEvaluation v

 theorem arityOfEvaluation {n : Nat} (raw : Program n) (v : List.Vector Nat n) :
    evaluate (arityOf raw) v = arityValue (evaluate raw v) := by
  simp only [arityOf, evalBranch, sameOfEvaluation, leftOfEvaluation,
    constantEvaluation, arityValue, tagValue]
  split_ifs <;> simp_all

 theorem firstOfEvaluation {n : Nat} (raw : Program n) (v : List.Vector Nat n) :
    evaluate (firstOf raw) v = firstValue (evaluate raw v) := by
  simp only [firstOf, evalBranch, sameOfEvaluation, leftOfEvaluation,
    rightOfEvaluation, constantEvaluation, firstValue, tagValue, payloadValue]
  split_ifs <;> simp_all

 theorem secondOfEvaluation {n : Nat} (raw : Program n) (v : List.Vector Nat n) :
    evaluate (secondOf raw) v = secondValue (evaluate raw v) := by
  simp only [secondOf, evalBranch, sameOfEvaluation, leftOfEvaluation,
    rightOfEvaluation, constantEvaluation, secondValue, tagValue, payloadValue]
  split_ifs <;> simp_all

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSelectorProof
