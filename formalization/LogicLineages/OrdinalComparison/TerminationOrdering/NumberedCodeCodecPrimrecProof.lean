module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCodePresentationProof

theorem codeEncoderPrimitive : NumberedCodeCodecPrimrecTargets.ActualCodeEncoderPrimitive := by
  intro n
  exact (Primrec.encode : Primrec (Encodable.encode : Code (Fin n) → Nat))

theorem codeDecoderPrimitive : NumberedCodeCodecPrimrecTargets.ActualCodeDecoderPrimitive := by
  intro n
  exact (Primrec.decode : Primrec (Encodable.decode : Nat → Option (Code (Fin n))))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecProof
