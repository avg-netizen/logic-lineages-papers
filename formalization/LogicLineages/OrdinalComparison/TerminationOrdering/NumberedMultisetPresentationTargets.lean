module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationTargets
open Source NumberedRewriteReduction NumberedMultisetCertificate NumberedMultisetNumeric

def ActualPackedListEncoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (@packedListNumber n arity Gamma)

def ActualPackedListDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (decodePackedList n arity Gamma)

def ActualCertificateEncoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (@certificateNumber n arity Gamma)

def ActualCertificateDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (decodeCertificate n arity Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationTargets
