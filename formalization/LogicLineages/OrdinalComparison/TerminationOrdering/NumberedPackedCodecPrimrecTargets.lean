module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecTargets
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding

def ActualPackedEncoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (@packedNumber n arity Gamma)

def ActualPackedDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (decodePackedNumber n arity Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecTargets
