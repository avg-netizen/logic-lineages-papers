module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ArgumentsProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Continuation20261114.OriginalHeadEncodingBridge.NativeProof (chooseEvaluation projectionOne typeEncoding)

theorem payloadEvaluation (n : Nat) (arity : Fin n → Nat) (tag raw : Nat) :
    evaluate (atPayload n arity tag) (raw ::ᵥ nil) =
    evaluate (branchArguments n arity tag) ((Nat.unpair raw).2 ::ᵥ nil) := by
  rw [atPayload,unaryCompositionEvaluation,rightEvaluation]
  rfl

theorem applicationValue (n : Nat) (arity : Fin n → Nat) (a b : Nat) :
    evaluate (branchArguments n arity 4) (Nat.pair a b ::ᵥ nil) = numbersNumber [1 + Nat.pair a b,a] := by
  simp only [branchArguments,consOfEvaluation,succOfEvaluation,projectionOne,leftEvaluation,Nat.unpair_pair,constantEvaluation]
  simp [numbersNumber,Nat.add_comm]

theorem rankedValue (n : Nat) (arity : Fin n → Nat) (s : Fin n) :
    evaluate (branchArguments n arity 5) (s.val ::ᵥ nil) = numbersNumber (List.replicate (arity s) 0) := by
  rw [branchArguments,unaryCompositionEvaluation,ListProof.arityValue]
  exact ListProof.groundListValue (arity s)

theorem typesEncoding (xs : List Ty) : typesNumber xs = numbersNumber (xs.map typeNumber) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp only [typesNumber,List.map_cons,numbersNumber,ih]

theorem nativeArguments (n : Nat) (arity : Fin n → Nat) (h : HeadCode (Fin n)) :
    evaluate (arguments n arity) (headNumber h ::ᵥ nil) =
    typesNumber (Source.SourceMarkedSyntax.headArguments arity (decodeHead h)) := by
  cases h <;>
    simp [arguments,chooseEvaluation,headNumber,Nat.unpair_pair,payloadEvaluation,
      applicationValue,rankedValue,constantEvaluation,
      decodeHead,Source.SourceMarkedSyntax.headArguments,typesEncoding,typeNumber,
      List.map_replicate] <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ArgumentsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ArgumentsProof
