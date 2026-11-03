module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecTargets
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedTypeCodecPrimrec

def ActualTypeEncoderPrimitive : Prop := Primrec typeNumber

def ActualTypeDecoderPrimitive : Prop := Primrec decodeType

def ActualTypeListParserCalibration : Prop := ∀ fuel value, typesParse fuel value =
  (NumberedMultisetNumeric.numbersParse fuel value).map (List.map typeEquiv.symm)

def ActualTypeListEncoderPrimitive : Prop := Primrec typesNumber

def ActualTypeListDecoderPrimitive : Prop := Primrec decodeTypes

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecTargets
