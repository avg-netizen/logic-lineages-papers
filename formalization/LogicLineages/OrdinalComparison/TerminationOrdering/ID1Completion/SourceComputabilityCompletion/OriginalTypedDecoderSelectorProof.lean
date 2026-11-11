module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderSelectorProof
open OriginalTypedDecoder OriginalTypedDecoderEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem statusEvaluation (v : List.Vector Nat 1) : evaluate status v = (Nat.unpair (v.get 0)).1 := leftEvaluation v
 theorem workEvaluation (v : List.Vector Nat 1) : evaluate work v = (Nat.unpair (v.get 0)).2 := rightEvaluation v
 theorem currentRequestEvaluation (v : List.Vector Nat 1) :
    evaluate currentRequest v = (Nat.unpair (evaluate work v - 1)).1 := by rw [currentRequest, headOfEvaluation]
 theorem restEvaluation (v : List.Vector Nat 1) :
    evaluate rest v = (Nat.unpair (evaluate work v - 1)).2 := by rw [rest, tailOfEvaluation]

 theorem modeEvaluation (v : List.Vector Nat 1) :
    evaluate mode v = requestMode (evaluate currentRequest v) := by
  simp only [mode, leftOfEvaluation, rightOfEvaluation, requestMode]

 theorem gammaEvaluation (v : List.Vector Nat 1) :
    evaluate gamma v = requestGamma (evaluate currentRequest v) := by
  simp only [gamma, leftOfEvaluation, rightOfEvaluation, requestGamma]

 theorem typEvaluation (v : List.Vector Nat 1) :
    evaluate typ v = requestType (evaluate currentRequest v) := by
  simp only [typ, leftOfEvaluation, rightOfEvaluation, requestType]

 theorem rawEvaluation (v : List.Vector Nat 1) :
    evaluate raw v = requestRaw (evaluate currentRequest v) := by
  simp only [raw, leftOfEvaluation, rightOfEvaluation, requestRaw]

 theorem tagEvaluation (v : List.Vector Nat 1) :
    evaluate tag v = (Nat.unpair (evaluate raw v)).1 := by
  simp only [tag, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem payloadEvaluation (v : List.Vector Nat 1) :
    evaluate payload v = (Nat.unpair (evaluate raw v)).2 := by
  simp only [payload, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem domainEvaluation (v : List.Vector Nat 1) :
    evaluate domain v = (Nat.unpair (evaluate payload v)).1 := by
  simp only [domain, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem unaryChildEvaluation (v : List.Vector Nat 1) :
    evaluate unaryChild v = (Nat.unpair (evaluate payload v)).2 := by
  simp only [unaryChild, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem firstChildEvaluation (v : List.Vector Nat 1) :
    evaluate firstChild v = (Nat.unpair (Nat.unpair (evaluate payload v)).2).1 := by
  simp only [firstChild, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem secondChildEvaluation (v : List.Vector Nat 1) :
    evaluate secondChild v = (Nat.unpair (Nat.unpair (evaluate payload v)).2).2 := by
  simp only [secondChild, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem expectedDomainEvaluation (v : List.Vector Nat 1) :
    evaluate expectedDomain v = (Nat.unpair (evaluate typ v - 1)).1 := by
  simp only [expectedDomain, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem expectedTailEvaluation (v : List.Vector Nat 1) :
    evaluate expectedTail v = (Nat.unpair (evaluate typ v - 1)).2 := by
  simp only [expectedTail, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem numberedHeadEvaluation (v : List.Vector Nat 1) :
    evaluate numberedHead v = (Nat.unpair (Nat.unpair (evaluate payload v)).2).1 := by
  simp only [numberedHead, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem numberedTypeEvaluation (v : List.Vector Nat 1) :
    evaluate numberedType v = (Nat.unpair (Nat.unpair (Nat.unpair (evaluate payload v)).2).2).1 := by
  simp only [numberedType, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem numberedBaseEvaluation (v : List.Vector Nat 1) :
    evaluate numberedBase v = (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (evaluate payload v)).2).2).2).1 := by
  simp only [numberedBase, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem numberedTypesEvaluation (v : List.Vector Nat 1) :
    evaluate numberedTypes v = (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (evaluate payload v)).2).2).2).2).1 := by
  simp only [numberedTypes, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

 theorem numberedExtrasEvaluation (v : List.Vector Nat 1) :
    evaluate numberedExtras v = (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (evaluate payload v)).2).2).2).2).2 := by
  simp only [numberedExtras, leftOfEvaluation, rightOfEvaluation, headOfEvaluation, tailOfEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderSelectorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderSelectorProof
