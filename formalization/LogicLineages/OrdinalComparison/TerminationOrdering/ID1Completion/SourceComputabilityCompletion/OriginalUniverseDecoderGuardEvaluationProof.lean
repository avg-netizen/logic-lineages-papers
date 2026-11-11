module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardEvaluationProof
open OriginalUniverseDecoder OriginalTypedDecoderEvaluationSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem modeEvaluation (v : List.Vector Nat 2) :
    evaluate mode v = OriginalTypedDecoder.requestMode (v.get 0) := by
  rw [mode,leftOfEvaluation]
  rfl

theorem typEvaluation (v : List.Vector Nat 2) :
    evaluate typ v = OriginalTypedDecoder.requestType (v.get 0) := by
  simp only [typ,leftOfEvaluation,rightOfEvaluation]
  rfl

theorem rawEvaluation (v : List.Vector Nat 2) :
    evaluate raw v = OriginalTypedDecoder.requestRaw (v.get 0) := by
  simp only [raw,rightOfEvaluation]
  rfl

theorem tagEvaluation (v : List.Vector Nat 2) :
    evaluate tag v = (Nat.unpair (OriginalTypedDecoder.requestRaw (v.get 0))).1 := by
  rw [tag,leftOfEvaluation,rawEvaluation]

theorem payloadEvaluation (v : List.Vector Nat 2) :
    evaluate payload v = (Nat.unpair (OriginalTypedDecoder.requestRaw (v.get 0))).2 := by
  rw [payload,rightOfEvaluation,rawEvaluation]

theorem domainEvaluation (v : List.Vector Nat 2) :
    evaluate domain v = (Nat.unpair (Nat.unpair (OriginalTypedDecoder.requestRaw (v.get 0))).2).1 := by
  rw [domain,leftOfEvaluation,payloadEvaluation]

theorem numberedHeadEvaluation (v : List.Vector Nat 2) :
    evaluate numberedHead v =
      (Nat.unpair (Nat.unpair (Nat.unpair (OriginalTypedDecoder.requestRaw (v.get 0))).2).2).1 := by
  rw [numberedHead,leftOfEvaluation,rightOfEvaluation,payloadEvaluation]

theorem memberAtEvaluation (M type : Program 2) (v : List.Vector Nat 2) :
    evaluate (memberAt M type) v = programValue2 M (evaluate type v) (v.get 1) := by
  rw [memberAt,binaryCompositionEvaluation]
  rfl

theorem windowAtEvaluation (W head : Program 2) (v : List.Vector Nat 2) :
    evaluate (windowAt W head) v = programValue2 W (evaluate head v) (v.get 1) := by
  rw [windowAt,binaryCompositionEvaluation]
  rfl

theorem oneIfEvaluation (test : Program 2) (v : List.Vector Nat 2) :
    evaluate (oneIf test) v = if evaluate test v = 1 then 1 else 0 := by
  simp only [oneIf,ifSameEvaluation,constantEvaluation]

theorem guardEvaluation (M W : Program 2) (v : List.Vector Nat 2) :
    evaluate (guard M W) v = guardValue (programValue2 M) (programValue2 W) (v.get 0) (v.get 1) := by
  simp only [OriginalUniverseDecoder.guard,extraGuard,ifSameEvaluation,constantEvaluation,memberAtEvaluation,
    windowAtEvaluation,oneIfEvaluation,modeEvaluation,typEvaluation,tagEvaluation,
    domainEvaluation,numberedHeadEvaluation,guardValue]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardEvaluationProof
