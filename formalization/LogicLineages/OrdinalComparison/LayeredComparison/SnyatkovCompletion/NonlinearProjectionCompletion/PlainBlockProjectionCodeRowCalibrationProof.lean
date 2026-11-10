module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
open PlainBlockProjectionCode

theorem weightedFold_calibration (sign : Int → Nat) (xs : List (Int × NormalForm.Summand)) :
    (xs.map (fun a => (a.1, a.2.data))).foldr
      (fun a rest => WindowCode.add (WindowCode.multiply (sign a.1) (NormalForm.Code.itemTerm a.2)) rest)
      (WindowCode.numeral 0) =
    (xs.foldr (fun a rest => Term.add (.multiply (sign a.1) a.2.term) rest) (.numeral 0)).encode := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, Term.encode]
      rw [NormalFormCodeProof.item_term, ih]
      rfl
#print axioms weightedFold_calibration

theorem positiveTerm_calibration (r : BlockRows.Row) :
    positiveTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.positiveTerm r).encode := by
  unfold positiveTerm BlockRowSubstitutionCode.rowData BlockRows.positiveTerm
  rw [weightedFold_calibration]
  rfl
#print axioms positiveTerm_calibration

theorem negativeTerm_calibration (r : BlockRows.Row) :
    negativeTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.negativeTerm r).encode := by
  unfold negativeTerm BlockRowSubstitutionCode.rowData BlockRows.negativeTerm
  rw [weightedFold_calibration (fun z : Int => (-z).toNat) r.2]
  rfl
#print axioms negativeTerm_calibration

theorem absoluteTerm_calibration (r : BlockRows.Row) :
    absoluteTerm (BlockRowSubstitutionCode.rowData r) = (BlockRows.absoluteTerm r).encode := by
  unfold absoluteTerm BlockRows.absoluteTerm
  rw [positiveTerm_calibration, negativeTerm_calibration]
  rfl
#print axioms absoluteTerm_calibration

theorem literalTermCalibration : PlainBlockProjectionCodeTargets.LiteralTermCalibration := fun r => ⟨positiveTerm_calibration r, negativeTerm_calibration r, absoluteTerm_calibration r⟩
#print axioms literalTermCalibration

theorem literalAtomCalibration : PlainBlockProjectionCodeTargets.LiteralAtomCalibration := by
  intro a
  cases a with
  | nonnegative r =>
      change WindowCode.atMost (negativeTerm (BlockRowSubstitutionCode.rowData r))
        (positiveTerm (BlockRowSubstitutionCode.rowData r)) = _
      rw [negativeTerm_calibration, positiveTerm_calibration]
      rfl
  | divisible m r =>
      change 8 * Nat.pair (m + 1) (absoluteTerm (BlockRowSubstitutionCode.rowData r)) + 4 = _
      rw [absoluteTerm_calibration]
      rfl
#print axioms literalAtomCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
