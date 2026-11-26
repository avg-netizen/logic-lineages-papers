module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericDecodingSupportProof NumberedNumericDecodingProof OriginalTypedDecoder

/-- Every raw context coordinate is the code of an original Encodable Gamma. -/
theorem contextEncodingSurjective : Function.Surjective (Encodable.encode (α := List Ty)) := by
  intro value
  induction value using Nat.strong_induction_on with
  | h value ih =>
    cases value with
    | zero => exact ⟨[], rfl⟩
    | succ value =>
      have ht : (Nat.unpair value).2 < value + 1 := by
        have hb := Nat.right_le_pair (Nat.unpair value).1 (Nat.unpair value).2
        rw [Nat.pair_unpair] at hb
        omega
      obtain ⟨Gamma, hGamma⟩ := ih (Nat.unpair value).2 ht
      obtain ⟨tau, _, htau⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (Nat.unpair value).1
      refine ⟨tau :: Gamma, ?_⟩
      rw [OriginalContextExtensionCalibrationProof.contextEncoding, htau, hGamma,
        Nat.pair_unpair]

/-- This converse is justified by the original total context codec, rather
than an invalid generic Encodable.decode/encode converse. -/
theorem contextDecodeSound (value : Nat) (Gamma : List Ty)
    (h : Encodable.decode (α := List Ty) value = some Gamma) :
    Encodable.encode Gamma = value := by
  obtain ⟨Delta, hDelta⟩ := contextEncodingSurjective value
  rw [← hDelta, Encodable.encodek] at h
  have he : Delta = Gamma := Option.some.inj h
  simpa only [he] using hDelta

theorem typeDecodeSound (value : Nat) (tau : Ty)
    (h : decodeType value = some tau) : typeNumber tau = value := by
  simp only [decodeType, Option.filter_eq_some_iff, decide_eq_true_eq] at h
  exact h.2

theorem typesDecodeSound (value : Nat) (types : List Ty)
    (h : decodeTypes value = some types) : typesNumber types = value := by
  simp only [decodeTypes, Option.filter_eq_some_iff, decide_eq_true_eq] at h
  exact h.2

theorem requestReconstruction (value : Nat) :
    Nat.pair (requestMode value)
      (Nat.pair (requestGamma value) (Nat.pair (requestType value) (requestRaw value))) = value := by
  simp only [requestMode, requestGamma, requestType, requestRaw, Nat.pair_unpair]

theorem requestRoundTrip (n : Nat) (request : NumberedTypedRequests.Request n) :
    decodeRequest n (encodeRequest request) = some request := by
  cases request <;>
    simp [decodeRequest, encodeRequest, termRequestValue, argumentsRequestValue,
      requestMode, requestGamma, requestType, requestRaw, Encodable.encodek,
      codeRoundTrip, typeRoundTrip, typesRoundTrip]

theorem requestDecodeSound (n value : Nat) (request : NumberedTypedRequests.Request n)
    (h : decodeRequest n value = some request) : encodeRequest request = value := by
  cases hg : Encodable.decode (α := List Ty) (requestGamma value) with
  | none => simp [decodeRequest, hg] at h
  | some Gamma =>
    cases hc : decodeCode n (requestRaw value) with
    | none => simp [decodeRequest, hg, hc] at h
    | some code =>
      by_cases hm : requestMode value = 0
      · cases ht : decodeType (requestType value) with
        | none => simp [decodeRequest, hg, hc, hm, ht] at h
        | some tau =>
          have hr : NumberedTypedRequests.Request.term Gamma tau code = request := by
            simpa [decodeRequest, hg, hc, hm, ht] using h
          rw [← hr]
          change Nat.pair 0 (Nat.pair (Encodable.encode Gamma)
            (Nat.pair (typeNumber tau) (codeNumber code))) = value
          rw [contextDecodeSound _ Gamma hg, typeDecodeSound _ tau ht,
            codeNumericSound n _ code hc]
          simpa only [hm] using requestReconstruction value
      · by_cases ha : requestMode value = 1
        · cases ht : decodeTypes (requestType value) with
          | none => simp [decodeRequest, hg, hc, hm, ha, ht] at h
          | some types =>
            have hr : NumberedTypedRequests.Request.arguments Gamma types code = request := by
              simpa [decodeRequest, hg, hc, hm, ha, ht] using h
            rw [← hr]
            change Nat.pair 1 (Nat.pair (Encodable.encode Gamma)
              (Nat.pair (typesNumber types) (codeNumber code))) = value
            rw [contextDecodeSound _ Gamma hg, typesDecodeSound _ types ht,
              codeNumericSound n _ code hc]
            simpa only [ha] using requestReconstruction value
        · simp [decodeRequest, hg, hc, hm, ha] at h

theorem actualOriginalTypedRequestCodec :
    OriginalTypedDecoderTargets.ActualOriginalTypedRequestCodec :=
  ⟨requestRoundTrip, requestDecodeSound⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
