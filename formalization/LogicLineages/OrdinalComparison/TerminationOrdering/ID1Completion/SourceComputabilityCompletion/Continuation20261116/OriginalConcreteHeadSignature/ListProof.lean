module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ListProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalListCodecEvaluationProof

theorem stepValue (index : Nat) (previous : List Nat) :
    evaluate groundListStep (index ::ᵥ numbersNumber previous ::ᵥ nil) = numbersNumber (0 :: previous) := by
  change evaluate InternalListCodec.consCode (ofFn ![0,numbersNumber previous]) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo,consEvaluation]
  rfl

theorem groundListValue (count : Nat) :
    evaluate groundList (count ::ᵥ nil) = numbersNumber (List.replicate count 0) := by
  change Nat.rec (motive := fun _ => Nat) 0
    (fun index previous => evaluate groundListStep (index ::ᵥ previous ::ᵥ nil)) count = _
  induction count with
  | zero => rfl
  | succ count ih =>
    change evaluate groundListStep (count ::ᵥ Nat.rec (motive := fun _ => Nat) 0
      (fun index previous => evaluate groundListStep (index ::ᵥ previous ::ᵥ nil)) count ::ᵥ nil) = _
    rw [ih,stepValue,List.replicate_succ]

theorem arityValue (n : Nat) (arity : Fin n → Nat) (s : Fin n) :
    evaluate (arityAt n arity) (s.val ::ᵥ nil) = arity s := by
  rw [arityAt,binaryCompositionEvaluation,constantEvaluation]
  change evaluate InternalRawListRecursion.lookup (ofFn ![s.val,numbersNumber (List.ofFn arity)]) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo,Continuation20261114.ExchangeAnswerSlots.NativeProof.lookupEncoded,
    List.getD_eq_getElem (List.ofFn arity) 0 (by simpa using s.isLt)]
  simp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.ListProof
