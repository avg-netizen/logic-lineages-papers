module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderGuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTraversalProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedTypedRequests NumberedMultisetNumeric OriginalUniverseDecoder
open OriginalUniverseDecoderGuardCalibrationProof OriginalUniverseDecoderEncodedProof
open OriginalTypedDecoder (encodeState encodeRequest finishedValue failedState)

theorem traversal (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (fuel : Nat) (requests : List (Request n)) :
    finishedValue (iterateValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity) fuel
      (encodeState ⟨1,requests.map encodeRequest⟩) (Encodable.encode ctx)) =
      (NumberedUniverseEvaluation.evaluate arity ctx.1.1 ctx.1.2 fuel requests).toNat := by
  induction fuel generalizing requests with
  | zero =>
    cases requests <;>
      simp [iterateValue,finishedValue,encodeState,numbersNumber,NumberedUniverseEvaluation.evaluate]
  | succ fuel ih =>
    cases requests with
    | nil =>
      simp [encodeState,numbersNumber,emptyIteration,finishedValue,NumberedUniverseEvaluation.evaluate]
    | cons request rest =>
      rw [iterateSuccStart,encodedTransition]
      cases hg : NumberedUniverseRequests.guard arity ctx.1.1 ctx.1.2 request with
      | false =>
        simp [stateStep,guardEncoded,hg,failedState,encodeState,numbersNumber,
          (show Nat.pair 0 0 = 0 from rfl),failedIteration,finishedValue,
          NumberedUniverseEvaluation.evaluate]
      | true =>
        cases he : NumberedTypedRequests.expand arity request with
        | none =>
          simp [stateStep,guardEncoded,hg,OriginalTypedDecoder.stateStep,
            OriginalTypedDecoderExpansionProof.expansion,he,failedState,encodeState,numbersNumber,
            (show Nat.pair 0 0 = 0 from rfl),failedIteration,finishedValue,
            NumberedUniverseEvaluation.evaluate]
        | some children =>
          simpa [stateStep,guardEncoded,hg,OriginalTypedDecoder.stateStep,
            OriginalTypedDecoderExpansionProof.expansion,he,List.map_append,
            NumberedUniverseEvaluation.evaluate] using ih (children ++ rest)

theorem termEncoded (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)) :
    checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity)
      (OriginalTypedDecoder.termRequestValue (Encodable.encode Gamma) (typeNumber tau) (codeNumber code))
      (Encodable.encode ctx) =
        (NumberedUniverseRequests.valid arity ctx.1.1 ctx.1.2 (.term Gamma tau code)).toNat := by
  have hv := NumberedUniverseEvaluationProof.sufficientFuelExact n arity ctx.1.1 ctx.1.2
    (codeNumber code+1) [.term Gamma tau code]
    (by simpa [NumberedRequestWeight.workWeight,NumberedRequestWeight.requestWeight]
      using NumberedRequestNumericBoundProof.codeWeightBound n code)
  have he := traversal n arity ctx (codeNumber code+1) [.term Gamma tau code]
  rw [hv] at he
  simpa [checkValue,OriginalTypedDecoder.initialValue,encodeState,numbersNumber,encodeRequest] using he

theorem actualOriginalUniverseTraversal : OriginalUniverseDecoderTargets.ActualOriginalUniverseTraversal :=
  ⟨traversal,acceptanceImpliesTyped⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTraversalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTraversalProof
