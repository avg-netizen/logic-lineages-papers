module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionTraversalProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedTypedRequests NumberedMultisetNumeric OriginalTypedDecoder
open OriginalTypedDecoderExpansionProof OriginalTypedDecoderEncodedProof

theorem traversal (n : Nat) (arity : Fin n → Nat) (fuel : Nat)
    (requests : List (Request n)) :
    finishedValue (iterateValue (headSignatureValue n arity) fuel
      (encodeState ⟨1,requests.map encodeRequest⟩)) =
      (NumberedTypedEvaluation.evaluate arity fuel requests).toNat := by
  induction fuel generalizing requests with
  | zero =>
    cases requests <;>
      simp [iterateValue,finishedValue,encodeState,numbersNumber,NumberedTypedEvaluation.evaluate]
  | succ fuel ih =>
    cases requests with
    | nil =>
      simp [encodeState,numbersNumber,emptyIteration,finishedValue,NumberedTypedEvaluation.evaluate]
    | cons request rest =>
      rw [iterateSuccStart,encodedTransition]
      cases he : NumberedTypedRequests.expand arity request with
      | none =>
        simp [stateStep,expansion,he,failedState,encodeState,numbersNumber,
          (show Nat.pair 0 0 = 0 from rfl),failedIteration,finishedValue,NumberedTypedEvaluation.evaluate]
      | some children =>
        simpa [stateStep,expansion,he,List.map_append,NumberedTypedEvaluation.evaluate]
          using ih (children ++ rest)

theorem actualOriginalTypedExpansion : OriginalTypedDecoderTargets.ActualOriginalTypedExpansion :=
  ⟨expansion,traversal⟩

theorem termEncoded (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (tau : Ty) (code : Code (Fin n)) :
    checkValue (headSignatureValue n arity)
      (termRequestValue (Encodable.encode Gamma) (typeNumber tau) (codeNumber code)) =
      (decodeTerm arity Gamma tau code).isSome.toNat := by
  have hv := NumberedTypedEvaluationProof.sufficientFuelExact n arity (codeNumber code+1)
    [.term Gamma tau code]
    (by simpa [NumberedRequestWeight.workWeight,NumberedRequestWeight.requestWeight]
      using NumberedRequestNumericBoundProof.codeWeightBound n code)
  have he := traversal n arity (codeNumber code+1) [.term Gamma tau code]
  rw [hv] at he
  simpa [checkValue,initialValue,encodeState,numbersNumber,encodeRequest,
    NumberedTypedRequests.valid] using he

theorem argumentsEncoded (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (code : Code (Fin n)) :
    checkValue (headSignatureValue n arity)
      (argumentsRequestValue (Encodable.encode Gamma) (typesNumber types) (codeNumber code)) =
      (decodeArguments arity Gamma types code).isSome.toNat := by
  have hv := NumberedTypedEvaluationProof.sufficientFuelExact n arity (codeNumber code+1)
    [.arguments Gamma types code]
    (by simpa [NumberedRequestWeight.workWeight,NumberedRequestWeight.requestWeight]
      using NumberedRequestNumericBoundProof.codeWeightBound n code)
  have he := traversal n arity (codeNumber code+1) [.arguments Gamma types code]
  rw [hv] at he
  simpa [checkValue,initialValue,encodeState,numbersNumber,encodeRequest,
    NumberedTypedRequests.valid] using he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionTraversalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionTraversalProof
