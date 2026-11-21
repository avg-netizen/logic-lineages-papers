module
public import LogicLineages.PermittedControl.RawFieldComparisonFormTargets
import LogicLineages.PermittedControl.LongFieldTailCalibrationProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.RawComparisonProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem raw_cmp_notes (a b : NONote) :
    rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) =
      orderingCode (NONote.cmp a b) :=
  rawComparisonCorrect a.1 b.1

private theorem decode_field_code (H : ValueField) :
    decodeLongFieldCode (longFieldCode H) = rawFieldView H := by
  cases H with
  | iterate a => rfl
  | entry a lam mu =>
    have hl : rawNoteDecode (rawNoteEncode lam.1) = lam.1 := rawNoteDecodeEncode lam.1
    have hm : rawNoteDecode (rawNoteEncode mu.1) = mu.1 := rawNoteDecodeEncode mu.1
    change (a,some (rawNoteDecode (rawNoteEncode lam.1),rawNoteDecode (rawNoteEncode mu.1))) =
      (a,some (lam.1,mu.1))
    rw [hl,hm]

private theorem decode_form_code (R : ComparisonForm) :
    decodeRawComparisonForm (encodeComparisonForm R) = rawComparisonFormView R := by
  cases R with
  | const c => rfl
  | linear sign H =>
    change Sum.inr (sign,decodeLongFieldCode (longFieldCode H)) =
      Sum.inr (sign,rawFieldView H)
    rw [decode_field_code]

private theorem distinct_form_code (F G : ValueField) :
    rawDistinctForm (longFieldCode F) (longFieldCode G) = encodeComparisonForm (distinctForm F G) := by
  cases F with
  | iterate a =>
    cases G with
    | iterate b =>
      by_cases h : a ≤ b <;>
        simp [rawDistinctForm,longFieldCode,distinctForm,encodeComparisonForm,h]
    | entry b lq mq => rfl
  | entry a lp mp =>
    cases G with
    | iterate b =>
      by_cases h : b ≤ a <;>
        simp [rawDistinctForm,longFieldCode,distinctForm,encodeComparisonForm,h,
          omegaMultipleTailCode_calibrated,ordinal_add_note_code]
    | entry b lq mq =>
      simp only [rawDistinctForm,longFieldCode,one_ne_zero,ite_false,omegaMultipleTailCode_calibrated,
        ordinal_add_note_code,ordinal_sub_note_code,raw_cmp_notes,distinctForm]
      cases NONote.cmp (lq - (mq + omegaMultiple (a - b))) (lp - (mp + omegaMultiple (b - a))) <;>
        rfl

private theorem same_form_code (F G : ValueField) :
    rawSameForm (longFieldCode F) (longFieldCode G) = sameForm F G := by
  cases F with
  | iterate a =>
    cases G with
    | iterate b => rfl
    | entry b lq mq => rfl
  | entry a lp mp =>
    cases G with
    | iterate b => rfl
    | entry b lq mq =>
      simp only [rawSameForm,longFieldCode,one_ne_zero,ite_false,omegaMultipleTailCode_calibrated,
        ordinal_add_note_code,ordinal_sub_note_code,raw_cmp_notes,sameForm]
      cases NONote.cmp (lp - (mp + omegaMultiple (b - a))) (lq - (mq + omegaMultiple (a - b))) <;>
        rfl

theorem rawFieldComparisonFormCalibration : RawFieldComparisonFormCalibration := by
  refine ⟨decode_field_code,decode_form_code,?_⟩
  intro F G
  have hd := distinct_form_code F G
  refine ⟨hd,?_,same_form_code F G⟩
  rw [hd,decode_form_code]

end LogicLineages.PermittedControl.FieldComparison
