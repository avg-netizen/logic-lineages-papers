module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
open Source NumberedRewriteReduction NumberedPackedPresentationProof

theorem packedEncoderPrimitive : NumberedPackedCodecPrimrecTargets.ActualPackedEncoderPrimitive := by
  intro n arity Gamma
  exact (Primrec.encode : Primrec (Encodable.encode : Packed (Fin n) arity Gamma → Nat))

theorem packedDecoderPrimitive : NumberedPackedCodecPrimrecTargets.ActualPackedDecoderPrimitive := by
  intro n arity Gamma
  exact (Primrec.decode : Primrec (Encodable.decode : Nat → Option (Packed (Fin n) arity Gamma)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
