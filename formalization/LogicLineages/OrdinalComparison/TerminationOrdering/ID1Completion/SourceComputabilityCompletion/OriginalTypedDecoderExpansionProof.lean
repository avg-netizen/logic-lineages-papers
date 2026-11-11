module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetNumeric
open OriginalTypedDecoder

@[simp] theorem termMode (g t r : Nat) : requestMode (termRequestValue g t r) = 0 := by
  simp [requestMode,termRequestValue]
@[simp] theorem termGamma (g t r : Nat) : requestGamma (termRequestValue g t r) = g := by
  simp [requestGamma,termRequestValue]
@[simp] theorem termType (g t r : Nat) : requestType (termRequestValue g t r) = t := by
  simp [requestType,termRequestValue]
@[simp] theorem termRaw (g t r : Nat) : requestRaw (termRequestValue g t r) = r := by
  simp [requestRaw,termRequestValue]
@[simp] theorem argumentsMode (g t r : Nat) : requestMode (argumentsRequestValue g t r) = 1 := by
  simp [requestMode,argumentsRequestValue]
@[simp] theorem argumentsGamma (g t r : Nat) : requestGamma (argumentsRequestValue g t r) = g := by
  simp [requestGamma,argumentsRequestValue]
@[simp] theorem argumentsType (g t r : Nat) : requestType (argumentsRequestValue g t r) = t := by
  simp [requestType,argumentsRequestValue]
@[simp] theorem argumentsRaw (g t r : Nat) : requestRaw (argumentsRequestValue g t r) = r := by
  simp [requestRaw,argumentsRequestValue]

theorem typeNumberInj (a b : Ty) : typeNumber a = typeNumber b ↔ a = b :=
  NumberedTypeCodecPrimrec.typeEquiv.injective.eq_iff

theorem dropFront (index gamma : Nat) :
    dropValue (index+1) gamma = dropValue index (Nat.unpair (gamma-1)).2 := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change (Nat.unpair (dropValue (index+1) gamma - 1)).2 =
      (Nat.unpair (dropValue index (Nat.unpair (gamma-1)).2 - 1)).2
    rw [ih]

theorem dropNil (index : Nat) : dropValue index 0 = 0 := by
  induction index with
  | zero => rfl
  | succ index ih =>
    change (Nat.unpair (dropValue index 0 - 1)).2 = 0
    rw [ih]
    rfl

theorem variableEncoded (Gamma : List Ty) (tau : Ty) (index : Nat) :
    variableValue (typeNumber tau) index (Encodable.encode Gamma) =
      (decide (Gamma[index]? = some tau)).toNat := by
  have he := OriginalTypedDecoderEvaluationSupportProof.originalVariableEvaluation
    (List.Vector.ofFn ![typeNumber tau,index,Encodable.encode Gamma])
  have hc := OriginalVariableDecoderEvaluationProof.actualOriginalVariableDecoderCalibration
    Gamma tau index
  have hs := NumberedVariableDecoderPrimrecProof.variableSuccessCalibration Gamma tau index
  calc
    variableValue (typeNumber tau) index (Encodable.encode Gamma) =
        LogicLineages.ComputabilityKnowledge.GorbowPRProgram.evaluate OriginalVariableDecoder.check
          (List.Vector.ofFn ![typeNumber tau,index,Encodable.encode Gamma]) := he.symm
    _ = (decodeVariable Gamma tau index).isSome.toNat := hc
    _ = (decide (Gamma[index]? = some tau)).toNat := congrArg Bool.toNat hs

@[simp] theorem headEncoded {n : Nat} (arity : Fin n → Nat) (head : HeadCode (Fin n)) :
    headSignatureValue n arity (headNumber head) =
      1 + Nat.pair (typeNumber (headResult (decodeHead head)))
        (typesNumber (headArguments arity (decodeHead head))) := by
  simp [headSignatureValue,NumberedNumericDecodingSupportProof.headNumericRoundTrip]

theorem termExpansion (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (tau : Ty) (code : Code (Fin n)) :
    expandValue (headSignatureValue n arity) (encodeRequest (.term Gamma tau code)) =
      (NumberedTypedRequests.expand arity (.term Gamma tau code)).map (List.map encodeRequest) := by
  cases code with
  | var index =>
    simp [encodeRequest,expandValue,codeNumber,variableEncoded,NumberedTypedRequests.expand]
  | lam sigma body =>
    cases tau with
    | ground => simp [encodeRequest,expandValue,codeNumber,typeNumber,NumberedTypedRequests.expand]
    | arrow domain result =>
      by_cases hs : sigma = domain <;>
        simp [encodeRequest,expandValue,codeNumber,typeNumber,NumberedTypedRequests.expand,
          Nat.add_comm 1,typeNumberInj,eq_comm,hs,OriginalContextExtensionCalibrationProof.typeEncoding]
  | app sigma q a =>
    simp [encodeRequest,expandValue,codeNumber,typeNumber,NumberedTypedRequests.expand]
  | bottom result =>
    simp [encodeRequest,expandValue,codeNumber,NumberedTypedRequests.expand,typeNumberInj]
  | ordinary head base =>
    simp [encodeRequest,expandValue,codeNumber,NumberedTypedRequests.expand,
      Nat.add_comm 1,typeNumberInj]
  | numbered label head result base types extras =>
    simp [encodeRequest,expandValue,codeNumber,NumberedTypedRequests.expand,
      Nat.add_comm 1,typeNumberInj]
  | argumentsNil => simp [encodeRequest,expandValue,codeNumber,NumberedTypedRequests.expand]
  | argumentsCons sigma q rest => simp [encodeRequest,expandValue,codeNumber,NumberedTypedRequests.expand]

theorem argumentsExpansion (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (code : Code (Fin n)) :
    expandValue (headSignatureValue n arity) (encodeRequest (.arguments Gamma types code)) =
      (NumberedTypedRequests.expand arity (.arguments Gamma types code)).map (List.map encodeRequest) := by
  cases code <;> cases types <;>
    simp [encodeRequest,expandValue,codeNumber,typesNumber,NumberedTypedRequests.expand,
      Nat.add_comm 1,typeNumberInj,eq_comm]
  split <;> simp_all

theorem expansion (n : Nat) (arity : Fin n → Nat) (request : NumberedTypedRequests.Request n) :
    expandValue (headSignatureValue n arity) (encodeRequest request) =
      (NumberedTypedRequests.expand arity request).map (List.map encodeRequest) := by
  cases request with
  | term Gamma tau code => exact termExpansion n arity Gamma tau code
  | arguments Gamma types code => exact argumentsExpansion n arity Gamma types code

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
