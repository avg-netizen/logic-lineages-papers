module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationTargets
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCodePresentation

def ActualCodeEncodingCalibration : Prop := ∀ n (code : Code (Fin n)), (codeEncodable n).encode code=codeNumber code

def ActualCodeDecodeNormalization : Prop := ∀ n value, encdec n value =
  bif (decodeCode n value).isSome then value+1 else 0

def ActualCodePresentationPrimitive : Prop := ∀ n : Nat, Nat.Primrec (encdec n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationTargets
