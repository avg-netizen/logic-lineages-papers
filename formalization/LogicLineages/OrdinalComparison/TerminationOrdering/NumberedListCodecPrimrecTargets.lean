module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecTargets
open NumberedMultisetNumeric NumberedListCodecPrimrec

def ActualEncoderPrimitive : Prop := Primrec numbersNumber

def ActualTableCalibration : Prop := ∀ bound fuel value : Nat, value ≤ bound →
  ((parseTable bound fuel)[value]?).getD none = numbersParse fuel value

def ActualParserPrimitive : Prop := Primrec₂ numbersParse

def ActualDecoderPrimitive : Prop := Primrec decodeNumbers

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecTargets
