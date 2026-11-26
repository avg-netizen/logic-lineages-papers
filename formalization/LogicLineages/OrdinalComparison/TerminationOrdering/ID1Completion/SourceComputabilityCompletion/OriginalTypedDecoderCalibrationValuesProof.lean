module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionTraversalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationValuesProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding OriginalTypedDecoder
open OriginalTypedDecoderExpansionProof OriginalTypedDecoderExpansionTraversalProof
open OriginalTypedDecoderCodecProof OriginalTypedDecoderReconstructionProof
open OriginalTypedDecoderReconstructionLocalProof

theorem malformedCodeReject (n : Nat) (arity : Fin n → Nat) (request : Nat)
    (hc : decodeCode n (requestRaw request) = none) :
    checkValue (headSignatureValue n arity) request = 0 := by
  rcases checkBit (headSignatureValue n arity) request with h | h
  · exact h
  · obtain ⟨code,he⟩ := successfulCheck n arity request h
    rw [← he,NumberedNumericDecodingProof.codeRoundTrip] at hc
    cases hc

theorem termValue (n : Nat) (arity : Fin n → Nat) (typ raw gamma : Nat) :
    checkValue (headSignatureValue n arity) (termRequestValue gamma typ raw) =
      termDecoderValue n arity typ raw gamma := by
  obtain ⟨Gamma,hGamma⟩ := contextEncodingSurjective gamma
  obtain ⟨tau,ht,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal typ
  cases hc : decodeCode n raw with
  | none =>
    rw [malformedCodeReject n arity _ (by simpa only [termRaw] using hc)]
    simp [termDecoderValue,hc]
  | some code =>
    have hr := NumberedNumericDecodingProof.codeNumericSound n raw code hc
    rw [← hGamma,← he,← hr]
    simpa [termDecoderValue,Encodable.encodek,NumberedNumericDecodingSupportProof.typeRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip] using termEncoded n arity Gamma tau code

theorem argumentsValue (n : Nat) (arity : Fin n → Nat) (types raw gamma : Nat) :
    checkValue (headSignatureValue n arity) (argumentsRequestValue gamma types raw) =
      argumentsDecoderValue n arity types raw gamma := by
  obtain ⟨Gamma,hGamma⟩ := contextEncodingSurjective gamma
  obtain ⟨ts,ht⟩ := typesEncodingSurjective types
  cases hc : decodeCode n raw with
  | none =>
    rw [malformedCodeReject n arity _ (by simpa only [argumentsRaw] using hc)]
    simp [argumentsDecoderValue,hc]
  | some code =>
    have hr := NumberedNumericDecodingProof.codeNumericSound n raw code hc
    rw [← hGamma,← ht,← hr]
    simpa [argumentsDecoderValue,Encodable.encodek,NumberedNumericDecodingSupportProof.typesRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip] using argumentsEncoded n arity Gamma ts code

theorem packedValue (n : Nat) (arity : Fin n → Nat) (value gamma : Nat) :
    packedDecoderValue n arity value gamma =
      termDecoderValue n arity (Nat.unpair value).1 (Nat.unpair value).2 gamma := by
  obtain ⟨Gamma,hGamma⟩ := contextEncodingSurjective gamma
  rw [← hGamma]
  simp only [packedDecoderValue,termDecoderValue,Encodable.encodek]
  rw [← NumberedNumericTypedValidationProof.packedValidation]
  cases ht : decodeType (Nat.unpair value).1 with
  | none => simp [NumberedNumericTypedValidation.packedValid,ht]
  | some tau =>
    simp only [NumberedNumericTypedValidation.packedValid,ht]
    rw [NumberedNumericTypedValidationProof.termValidation]
    cases hc : decodeCode n (Nat.unpair value).2 <;> simp [hc]

theorem termReconstruction (n : Nat) (arity : Fin n → Nat) (typ raw gamma : Nat) :
    termDecoderValue n arity typ raw gamma = 1 ↔
      ∃ (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)),
        Encodable.encode Gamma = gamma ∧ typeNumber tau = typ ∧ codeNumber code = raw ∧
          (decodeTerm arity Gamma tau code).isSome = true := by
  constructor
  · intro h
    cases hg : Encodable.decode (α := List Ty) gamma with
    | none => simp [termDecoderValue,hg] at h
    | some Gamma =>
      cases ht : decodeType typ with
      | none => simp [termDecoderValue,hg,ht] at h
      | some tau =>
        cases hc : decodeCode n raw with
        | none => simp [termDecoderValue,hg,ht,hc] at h
        | some code =>
          refine ⟨Gamma,tau,code,contextDecodeSound _ _ hg,typeDecodeSound _ _ ht,
            NumberedNumericDecodingProof.codeNumericSound n raw code hc,?_⟩
          simpa [termDecoderValue,hg,ht,hc] using h
  · rintro ⟨Gamma,tau,code,rfl,rfl,rfl,h⟩
    simp [termDecoderValue,Encodable.encodek,NumberedNumericDecodingSupportProof.typeRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip,h]

theorem argumentsReconstruction (n : Nat) (arity : Fin n → Nat) (types raw gamma : Nat) :
    argumentsDecoderValue n arity types raw gamma = 1 ↔
      ∃ (Gamma ts : List Ty) (code : Code (Fin n)),
        Encodable.encode Gamma = gamma ∧ typesNumber ts = types ∧ codeNumber code = raw ∧
          (decodeArguments arity Gamma ts code).isSome = true := by
  constructor
  · intro h
    cases hg : Encodable.decode (α := List Ty) gamma with
    | none => simp [argumentsDecoderValue,hg] at h
    | some Gamma =>
      cases ht : decodeTypes types with
      | none => simp [argumentsDecoderValue,hg,ht] at h
      | some ts =>
        cases hc : decodeCode n raw with
        | none => simp [argumentsDecoderValue,hg,ht,hc] at h
        | some code =>
          refine ⟨Gamma,ts,code,contextDecodeSound _ _ hg,typesDecodeSound _ _ ht,
            NumberedNumericDecodingProof.codeNumericSound n raw code hc,?_⟩
          simpa [argumentsDecoderValue,hg,ht,hc] using h
  · rintro ⟨Gamma,ts,code,rfl,rfl,rfl,h⟩
    simp [argumentsDecoderValue,Encodable.encodek,NumberedNumericDecodingSupportProof.typesRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip,h]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationValuesProof
