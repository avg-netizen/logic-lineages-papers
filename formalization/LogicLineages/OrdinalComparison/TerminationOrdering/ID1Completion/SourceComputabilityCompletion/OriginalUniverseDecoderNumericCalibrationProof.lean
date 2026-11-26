module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderReconstructionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderNumericCalibrationProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding OriginalUniverseDecoder OriginalUniverseDecoderReconstructionProof
open OriginalUniverseDecoderTraversalProof
open OriginalTypedDecoder (termRequestValue)

/-- A guarded acceptance cannot repair malformed ORIGINAL raw syntax. -/
theorem malformedCodeReject (n : Nat) (arity : Fin n → Nat) (typ raw gamma context : Nat)
    (hc : decodeCode n raw = none) :
    checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity) (termRequestValue gamma typ raw) context = 0 := by
  rcases checkBit (OriginalTypedDecoder.headSignatureValue n arity)
    (contextMemberValue n) (headWindowValue n arity) (termRequestValue gamma typ raw) context with hz | ho
  · exact hz
  · obtain ⟨ctx,Gamma,tau,code,he,hg,ht,hr,hv⟩ :=
      (termReconstruction n arity typ raw gamma context).mp ho
    rw [← hr,NumberedNumericDecodingProof.codeRoundTrip] at hc
    cases hc

/-- The original guarded numeric validator, including malformed raw codes. -/
theorem termNumericCalibration (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (tau : Ty) (raw : Nat) :
    checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity)
      (termRequestValue (Encodable.encode Gamma) (typeNumber tau) raw) (Encodable.encode ctx) =
      (NumberedUniverseNumericValidation.termValid n arity ctx.1.1 ctx.1.2 Gamma tau raw).toNat := by
  rw [NumberedUniverseNumericValidationProof.termValidation]
  cases hc : decodeCode n raw with
  | none =>
    rw [malformedCodeReject n arity _ _ _ _ hc]
    simp [hc]
  | some code =>
    have hr := NumberedNumericDecodingProof.codeNumericSound n raw code hc
    rw [← hr,termEncoded]
    simp [NumberedNumericDecodingProof.codeRoundTrip,NumberedUniverseRequests.valid]

/-- ORIGINAL packed pairing with no extra decoding or window premise. -/
theorem packedNumericCalibration (n : Nat) (arity : Fin n → Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) (value : Nat) :
    checkValue (OriginalTypedDecoder.headSignatureValue n arity)
      (contextMemberValue n) (headWindowValue n arity)
      (termRequestValue (Encodable.encode Gamma) (Nat.unpair value).1 (Nat.unpair value).2)
      (Encodable.encode ctx) =
      (NumberedUniverseNumericValidation.packedValid n arity ctx.1.1 ctx.1.2 Gamma value).toNat := by
  obtain ⟨tau,ht,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (Nat.unpair value).1
  simp only [NumberedUniverseNumericValidation.packedValid,ht,Option.any_some]
  rw [← he]
  exact termNumericCalibration n arity ctx Gamma tau _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderNumericCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderNumericCalibrationProof
