module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecProof
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep NumberedStepCodecPrimrec NumberedStepCodecPrimrecSupportProof

theorem positionEncoderPrimitive : NumberedStepCodecPrimrecTargets.ActualPositionEncoderPrimitive := positionEncoder
theorem positionDecoderPrimitive : NumberedStepCodecPrimrecTargets.ActualPositionDecoderPrimitive := positionDecoder

theorem pathEncoderPrimitive : NumberedStepCodecPrimrecTargets.ActualPathEncoderPrimitive :=
  NumberedListCodecPrimrecProof.encoderPrimitive.comp
    (Primrec.list_map Primrec.id (positionEncoder.comp Primrec.snd).to₂)

theorem pathDecoderPrimitive : NumberedStepCodecPrimrecTargets.ActualPathDecoderPrimitive :=
  Primrec.option_bind NumberedListCodecPrimrecProof.decoderPrimitive (positionsDecoder.comp Primrec.snd).to₂

theorem stepEncoderPrimitive : NumberedStepCodecPrimrecTargets.ActualStepEncoderPrimitive :=
  Primrec₂.natPair.comp (pathEncoderPrimitive.comp (Primrec.fst.comp certificateTo))
    (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp certificateTo))
      (Primrec.snd.comp (Primrec.snd.comp certificateTo)))

theorem stepDecoderPrimitive : NumberedStepCodecPrimrecTargets.ActualStepDecoderPrimitive := by
  apply Primrec.option_map (pathDecoderPrimitive.comp (Primrec.fst.comp Primrec.unpair))
  exact (certificateFrom.comp (Primrec.snd.pair
    ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))).pair
     (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))))))).to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecProof
