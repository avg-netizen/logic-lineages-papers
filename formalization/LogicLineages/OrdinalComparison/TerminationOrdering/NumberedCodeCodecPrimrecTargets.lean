module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodePresentationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecTargets
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCodePresentationProof

def ActualCodeEncoderPrimitive : Prop := ∀ n : Nat, Primrec (@codeNumber n)

def ActualCodeDecoderPrimitive : Prop := ∀ n : Nat, Primrec (decodeCode n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeCodecPrimrecTargets
