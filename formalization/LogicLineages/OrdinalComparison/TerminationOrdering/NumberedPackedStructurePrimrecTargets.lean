module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding

def ActualPackedCodePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (@packedCode (Fin n) arity Gamma)

def ActualStructuralDecodeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (c : Ty × Code (Fin n)),
    decodePackedNumber n arity Gamma (Nat.pair (typeNumber c.1) (codeNumber c.2)) =
      decodePacked arity Gamma c

def ActualStructuralDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (decodePacked arity Gamma : Ty × Code (Fin n) → Option (Packed (Fin n) arity Gamma))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecTargets
