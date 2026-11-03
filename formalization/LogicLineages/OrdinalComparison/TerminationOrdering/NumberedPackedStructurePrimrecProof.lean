module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding

theorem packedCodePrimitive : NumberedPackedStructurePrimrecTargets.ActualPackedCodePrimitive := by
  intro n arity Gamma
  apply Primrec.encode_iff.mp
  exact NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma

theorem structuralDecodeCalibration : NumberedPackedStructurePrimrecTargets.ActualStructuralDecodeCalibration := by
  intro n arity Gamma c
  rcases c with ⟨tau, code⟩
  have ht : decodeType (typeNumber tau) = some tau :=
    NumberedNumericDecodingProof.typeNumericRoundTrip tau
  cases hq : decodeTerm arity Gamma tau code with
  | none =>
    simp [decodePackedNumber, packedParse, ht,
      NumberedNumericDecodingProof.codeRoundTrip, decodePacked, hq]
  | some q =>
    have hc := NumberedAuxiliaryDecodingProof.termDecodeSound (Fin n) arity Gamma tau code q hq
    simp [decodePackedNumber, packedParse, ht,
      NumberedNumericDecodingProof.codeRoundTrip, decodePacked, hq, packedNumber, hc]

theorem structuralDecoderPrimitive : NumberedPackedStructurePrimrecTargets.ActualStructuralDecoderPrimitive := by
  intro n arity Gamma
  have hcode : Primrec (fun c : Ty × Code (Fin n) =>
      Nat.pair (typeNumber c.1) (codeNumber c.2)) := Primrec.encode
  exact ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp hcode).of_eq
    (fun c => structuralDecodeCalibration n arity Gamma c)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
