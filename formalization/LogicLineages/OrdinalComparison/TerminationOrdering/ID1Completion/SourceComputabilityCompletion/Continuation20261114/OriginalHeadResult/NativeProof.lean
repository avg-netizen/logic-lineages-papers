module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHeadEncodingBridge.NativeProof (chooseEvaluation projectionOne typeEncoding)

theorem arrowEvaluation (p q : Program 1) (v : List.Vector Nat 1) :
    evaluate (arrow p q) v = 1 + Nat.pair (evaluate p v) (evaluate q v) := by
  change evaluate (InternalApplicationCertificateConstructors.pairOf p q) v + 1 = _
  rw [pairOfEvaluation,Nat.add_comm]

theorem payloadEvaluation (tag raw : Nat) :
    evaluate (atPayload tag) (raw ::ᵥ List.Vector.nil) =
    evaluate (branchResult tag) ((Nat.unpair raw).2 ::ᵥ List.Vector.nil) := by
  rw [atPayload,unaryCompositionEvaluation,rightEvaluation]
  rfl

theorem nativeHeadResult : Targets.NativeHeadResult := by
  intro n h
  change evaluate headResult (headNumber h ::ᵥ List.Vector.nil) =
    Encodable.encode (Source.SourceMarkedSyntax.headResult (NumberedAuxiliaryDecoding.decodeHead h))
  cases h <;>
    simp [headResult,chooseEvaluation,headNumber,Nat.unpair_pair,payloadEvaluation,
      branchResult,arrowEvaluation,constantEvaluation,projectionOne,rightEvaluation,
      NumberedAuxiliaryDecoding.decodeHead,Source.SourceMarkedSyntax.headResult,
      Ty.caseType,Ty.recType,typeEncoding,typeNumber]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
