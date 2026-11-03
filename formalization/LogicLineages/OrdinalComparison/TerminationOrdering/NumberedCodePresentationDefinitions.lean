module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentation
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding

def codeEncodable (n : Nat) : Encodable (Code (Fin n)) where
  encode := codeNumber
  decode := decodeCode n
  encodek := NumberedNumericDecodingProof.codeRoundTrip n

def encdec (n value : Nat) : Nat :=
  letI := codeEncodable n
  Encodable.encode (decodeCode n value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentation
