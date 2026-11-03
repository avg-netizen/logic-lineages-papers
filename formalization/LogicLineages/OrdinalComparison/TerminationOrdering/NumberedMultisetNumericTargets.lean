module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetCertificate NumberedMultisetNumeric

def ActualNaturalListRoundTrip : Prop := ∀ xs : List Nat,decodeNumbers (numbersNumber xs)=some xs
def ActualNaturalListDecodeSound : Prop := ∀ (value : Nat) (xs : List Nat),decodeNumbers value=some xs → numbersNumber xs=value

def ActualPackedListRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (qs : List (Packed (Fin n) arity Gamma)),
  decodePackedList n arity Gamma (packedListNumber qs)=some qs

def ActualPackedListDecodeSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) (qs : List (Packed (Fin n) arity Gamma)),
  decodePackedList n arity Gamma value=some qs → packedListNumber qs=value

def ActualMultisetCertificateRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (c : MultisetCertificate n arity Gamma),
  decodeCertificate n arity Gamma (certificateNumber c)=some c

def ActualMultisetCertificateDecodeSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) (c : MultisetCertificate n arity Gamma),
  decodeCertificate n arity Gamma value=some c → certificateNumber c=value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTargets
