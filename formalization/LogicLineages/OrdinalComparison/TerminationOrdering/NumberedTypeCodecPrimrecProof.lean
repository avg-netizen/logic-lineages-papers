module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecProof
open Source NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetNumeric NumberedTypeCodecPrimrec NumberedTypeCodecPrimrecSupportProof

theorem typeEncoderPrimitive : NumberedTypeCodecPrimrecTargets.ActualTypeEncoderPrimitive := typeTo

theorem typeDecoderPrimitive : NumberedTypeCodecPrimrecTargets.ActualTypeDecoderPrimitive :=
  (Primrec.option_some.comp typeFrom).of_eq (fun value => (decodeTypeExact value).symm)

theorem typeListParserCalibration : NumberedTypeCodecPrimrecTargets.ActualTypeListParserCalibration := parserCalibration

theorem typeListEncoderPrimitive : NumberedTypeCodecPrimrecTargets.ActualTypeListEncoderPrimitive :=
  (NumberedListCodecPrimrecProof.encoderPrimitive.comp
    (Primrec.list_map Primrec.id (typeTo.comp Primrec.snd).to₂)).of_eq (fun types => (listCodeExact types).symm)

theorem typeListDecoderPrimitive : NumberedTypeCodecPrimrecTargets.ActualTypeListDecoderPrimitive := by
  have hmap : Primrec (List.map typeEquiv.symm) := Primrec.list_map Primrec.id (typeFrom.comp Primrec.snd).to₂
  exact (Primrec.option_map NumberedListCodecPrimrecProof.decoderPrimitive (hmap.comp Primrec.snd).to₂).of_eq
    (fun value => (decoderCalibration value).symm)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecProof
