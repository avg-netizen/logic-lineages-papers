module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedTypedRequests
open NumberedRequestWeight NumberedTypedEvaluation NumberedNumericTypedValidation

theorem termValidation : NumberedNumericTypedValidationTargets.ActualNumericTermValidation := by
  intro n arity Gamma tau value
  cases hc : decodeCode n value with
  | none => simp [termValid, hc]
  | some code =>
    have he := NumberedNumericDecodingProof.codeNumericSound n value code hc
    have hb := NumberedRequestNumericBoundProof.codeWeightBound n code
    rw [he] at hb
    have hw : workWeight [.term Gamma tau code] ≤ value + 1 := by
      simpa [workWeight, requestWeight] using hb
    have hv := NumberedTypedEvaluationProof.sufficientFuelExact n arity (value + 1)
      [.term Gamma tau code] hw
    simpa [termValid, hc, valid] using hv

theorem argumentsValidation : NumberedNumericTypedValidationTargets.ActualNumericArgumentsValidation := by
  intro n arity Gamma types value
  cases hc : decodeCode n value with
  | none => simp [argumentsValid, hc]
  | some code =>
    have he := NumberedNumericDecodingProof.codeNumericSound n value code hc
    have hb := NumberedRequestNumericBoundProof.codeWeightBound n code
    rw [he] at hb
    have hw : workWeight [.arguments Gamma types code] ≤ value + 1 := by
      simpa [workWeight, requestWeight] using hb
    have hv := NumberedTypedEvaluationProof.sufficientFuelExact n arity (value + 1)
      [.arguments Gamma types code] hw
    simpa [argumentsValid, hc, valid] using hv

private theorem packedParseReencode (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (value : Nat) (q : Packed (Fin n) arity Gamma)
    (h : packedParse n arity Gamma value = some q) : packedNumber q = value := by
  unfold packedParse at h
  cases ht : decodeType (Nat.unpair value).1 with
  | none => simp [ht] at h
  | some tau =>
    cases hc : decodeCode n (Nat.unpair value).2 with
    | none => simp [ht, hc] at h
    | some code =>
      cases hq : decodeTerm arity Gamma tau code with
      | none => simp [ht, hc, decodePacked, hq] at h
      | some term =>
        have heq : (⟨tau, term⟩ : Packed (Fin n) arity Gamma) = q := by
          simpa [ht, hc, decodePacked, hq] using h
        rw [← heq]
        have htype := NumberedRawParserSoundnessSupportProof.decodedType
          (Nat.unpair value).1 tau ht
        have hcode := NumberedNumericDecodingProof.codeNumericSound
          n (Nat.unpair value).2 code hc
        have hterm := NumberedAuxiliaryDecodingProof.termDecodeSound
          (Fin n) arity Gamma tau code term hq
        simp only [packedNumber, hterm, htype, hcode, Nat.pair_unpair]

private theorem packedFilter (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (value : Nat) :
    decodePackedNumber n arity Gamma value = packedParse n arity Gamma value := by
  cases hp : packedParse n arity Gamma value with
  | none => simp [decodePackedNumber, hp]
  | some q =>
    have he := packedParseReencode n arity Gamma value q hp
    simp [decodePackedNumber, hp, he]

theorem packedValidation : NumberedNumericTypedValidationTargets.ActualNumericPackedValidation := by
  intro n arity Gamma value
  rw [packedFilter]
  cases ht : decodeType (Nat.unpair value).1 with
  | none => simp [packedValid, packedParse, ht]
  | some tau =>
    simp only [packedValid, ht]
    rw [termValidation]
    cases hc : decodeCode n (Nat.unpair value).2 <;>
      simp [packedParse, ht, hc, decodePacked]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationProof
