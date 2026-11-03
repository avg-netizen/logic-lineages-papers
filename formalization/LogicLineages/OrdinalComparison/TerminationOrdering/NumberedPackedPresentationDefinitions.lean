module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentation
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding

/-- The original numeric codec supplies the actual packed typed syntax. -/
@[reducible] def packedEncodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Encodable (Packed (Fin n) arity Gamma) where
  encode := packedNumber
  decode := decodePackedNumber n arity Gamma
  encodek := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma

def encdec (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Nat :=
  letI := packedEncodable n arity Gamma
  Encodable.encode (decodePackedNumber n arity Gamma value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedPresentation
