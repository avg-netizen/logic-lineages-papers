module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecTargets
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedHeadCodecPrimrec

def ActualHeadEncoderPrimitive : Prop := ∀ n : Nat, Primrec (@headNumber n)

def ActualHeadParserPrimitive : Prop := ∀ n : Nat, Primrec (headParse n)

def ActualHeadDecoderPrimitive : Prop := ∀ n : Nat, Primrec (decodeHeadNumber n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecTargets
