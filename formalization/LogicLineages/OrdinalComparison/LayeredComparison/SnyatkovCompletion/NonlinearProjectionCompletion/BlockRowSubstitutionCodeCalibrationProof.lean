module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProof
open BlockRowSubstitutionCode

theorem item_name (s : NormalForm.Summand) : s.data.2.1 = s.name := by
  cases s <;> rfl
#print axioms item_name

theorem literalEntryCalibration : BlockRowSubstitutionCodeTargets.LiteralEntryCalibration := by
  intro i replacement positive negative es
  induction es with
  | nil => rfl
  | cons a es ih =>
      change step i replacement.encode (a.1, a.2.data)
        (entries i replacement.encode positive.encode negative.encode
          (es.map (fun a => (a.1, a.2.data)))) =
        rowData (BlockRows.substituteEntries i replacement positive negative (a :: es))
      rw [ih]
      conv_rhs => rw [BlockRows.substituteEntries]
      unfold step
      simp only [item_name]
      by_cases h : a.2.name = i
      · simp only [h, if_true, rowData, NormalFormCodeProof.item_term,
          WindowCodeProof.term_calibration, WindowCode.add, WindowCode.multiply, Term.encode] <;> rfl
      · simp only [h, if_false, rowData, List.map_cons] <;> rfl
#print axioms literalEntryCalibration

theorem literalRowCalibration : BlockRowSubstitutionCodeTargets.LiteralRowCalibration := by
  intro i replacement r
  change entries i replacement.encode
    (WindowCode.termSubstitute i replacement.encode r.1.1.encode)
    (WindowCode.termSubstitute i replacement.encode r.1.2.encode)
    (r.2.map (fun a => (a.1, a.2.data))) =
    rowData (BlockRows.substituteEntries i replacement
      (r.1.1.substitute i replacement) (r.1.2.substitute i replacement) r.2)
  rw [WindowCodeProof.term_calibration, WindowCodeProof.term_calibration]
  exact literalEntryCalibration i replacement _ _ r.2
#print axioms literalRowCalibration

theorem decode_rowData (r : BlockRows.Row) :
    decodeRow (Encodable.encode (rowData r)) = rowData r := by
  simp only [decodeRow, Encodable.encodek, Option.getD_some]
#print axioms decode_rowData

theorem literalEncodedCalibration : BlockRowSubstitutionCodeTargets.LiteralEncodedCalibration := by
  intro i replacement r
  unfold encoded
  rw [decode_rowData, literalRowCalibration]
#print axioms literalEncodedCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeProof
