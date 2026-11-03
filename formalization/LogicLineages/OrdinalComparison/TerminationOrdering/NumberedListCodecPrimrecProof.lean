module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
open NumberedMultisetNumeric NumberedListCodecPrimrec NumberedListCodecPrimrecSupportProof

theorem encoderPrimitive : NumberedListCodecPrimrecTargets.ActualEncoderPrimitive := by
  have h := Primrec.list_foldr (Primrec.id : Primrec (fun xs : List Nat => xs)) (Primrec.const 0)
    (Primrec.to₂ (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))
  exact h.of_eq (by intro xs; induction xs <;> simp_all [numbersNumber, Nat.add_comm])

theorem tableCalibration : NumberedListCodecPrimrecTargets.ActualTableCalibration := calibration

theorem parserPrimitive : NumberedListCodecPrimrecTargets.ActualParserPrimitive := by
  have h : Primrec₂ (fun fuel value => ((parseTable value fuel)[value]?).getD none) :=
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (tablePrimitive.comp Primrec.snd Primrec.fst) Primrec.snd)
      (Primrec.const none)).to₂
  exact h.of_eq (by intro fuel value; exact calibration value fuel value (Nat.le_refl _))

theorem decoderPrimitive : NumberedListCodecPrimrecTargets.ActualDecoderPrimitive :=
  parserPrimitive.comp Primrec.succ Primrec.id

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
