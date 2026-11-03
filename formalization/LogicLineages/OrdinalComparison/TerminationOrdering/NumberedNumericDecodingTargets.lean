module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding

def ActualTypeNumericRoundTrip : Prop := ∀ tau,decodeType (typeNumber tau)=some tau

def ActualTypeListNumericRoundTrip : Prop := ∀ types,decodeTypes (typesNumber types)=some types

def ActualCodeNumericRoundTrip : Prop := ∀ (n : Nat) (c : Code (Fin n)),decodeCode n (codeNumber c)=some c

def ActualCodeNumericSound : Prop := ∀ (n value : Nat) (c : Code (Fin n)),decodeCode n value=some c → codeNumber c=value

def ActualPackedNumericRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
  decodePackedNumber n arity Gamma (packedNumber q)=some q

def ActualPackedNumericSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) (q : Packed (Fin n) arity Gamma),
  decodePackedNumber n arity Gamma value=some q → packedNumber q=value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingTargets
