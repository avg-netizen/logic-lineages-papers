module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationTargets
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedPackedPresentation

def ActualPackedEncodingCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
    (packedEncodable n arity Gamma).encode q = packedNumber q

def ActualPackedDecodeNormalization : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat),
    encdec n arity Gamma value =
      bif (decodePackedNumber n arity Gamma value).isSome then value + 1 else 0

def ActualPackedPresentationPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Nat.Primrec (encdec n arity Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentationTargets
