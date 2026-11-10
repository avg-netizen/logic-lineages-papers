module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode


theorem isHead_calibration (i : Nat) (s : NormalForm.Summand) :
    isHead i s.data = PlainMaximum.isHead i s := by
  cases s <;> rfl
#print axioms isHead_calibration

theorem headCoefficient_calibration (i : Nat) (r : BlockRows.Row) :
    headCoefficient i (BlockRowSubstitutionCode.rowData r) = PlainMaximum.headCoefficient i r := by
  simp only [headCoefficient, BlockRowSubstitutionCode.rowData, List.map_map, Function.comp_def,
    isHead_calibration, PlainMaximum.headCoefficient]
#print axioms headCoefficient_calibration

theorem remainingOccurrences_calibration (i : Nat) (r : BlockRows.Row) :
    remainingOccurrences i (BlockRowSubstitutionCode.rowData r) =
      (PlainMaximum.remainingOccurrences i r).map (fun a => (a.1, a.2.data)) := by
  simp only [remainingOccurrences, BlockRowSubstitutionCode.rowData, List.filter_map, Function.comp_def,
    isHead_calibration, PlainMaximum.remainingOccurrences]
#print axioms remainingOccurrences_calibration

theorem mass_calibration (r : BlockRows.Row) : mass (BlockRowSubstitutionCode.rowData r) = PlainMaximum.mass r := by
  simp only [mass, BlockRowSubstitutionCode.rowData, List.map_map, Function.comp_def, PlainMaximum.mass]
#print axioms mass_calibration

theorem boundary_calibration (i : Nat) (r : BlockRows.Row) :
    boundary i (BlockRowSubstitutionCode.rowData r) = (PlainMaximum.boundary i r).encode := by
  unfold boundary
  rw [headCoefficient_calibration]
  rfl
#print axioms boundary_calibration

theorem literalRowCalibration : PlainBlockLinearizationCodeTargets.LiteralRowCalibration :=
  fun i r => ⟨headCoefficient_calibration i r, remainingOccurrences_calibration i r,
    mass_calibration r, boundary_calibration i r⟩
#print axioms literalRowCalibration

theorem positiveGuard_calibration (i : Nat) (r : BlockRows.Row) :
    positiveGuard i (BlockRowSubstitutionCode.rowData r) =
      BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.positiveGuard i r) := by
  unfold positiveGuard
  rw [boundary_calibration]
  rfl
#print axioms positiveGuard_calibration

theorem negativeGuard_calibration (i : Nat) (r : BlockRows.Row) :
    negativeGuard i (BlockRowSubstitutionCode.rowData r) =
      BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.negativeGuard i r) := by
  unfold negativeGuard
  rw [boundary_calibration]
  rfl
#print axioms negativeGuard_calibration

theorem linearizeNonnegative_calibration (i : Nat) (r : BlockRows.Row) :
    linearizeNonnegative i (BlockRowSubstitutionCode.rowData r) =
      BlockFormulaSubstitutionCode.formulaCode (PlainMaximum.linearizeNonnegative i r) := by
  unfold linearizeNonnegative PlainMaximum.linearizeNonnegative
  rw [headCoefficient_calibration]
  split_ifs
  · exact positiveGuard_calibration i r
  · exact negativeGuard_calibration i r
  · rw [remainingOccurrences_calibration]
    rfl
#print axioms linearizeNonnegative_calibration

theorem outsideRow_calibration (i : Nat) (r : BlockRows.Row) :
    outsideRow i (BlockRowSubstitutionCode.rowData r) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.outsideRow i r) := by
  unfold outsideRow PlainBlockSplit.outsideRow
  simp only [headCoefficient_calibration, boundary_calibration]
  split_ifs <;> rfl
#print axioms outsideRow_calibration

theorem bandCandidate_calibration (i : Nat) (r : BlockRows.Row) (d : Nat) :
    bandCandidate i (BlockRowSubstitutionCode.rowData r) d = (PlainBlockSplit.bandCandidate i r d).encode := by
  unfold bandCandidate
  rw [boundary_calibration]
  rfl
#print axioms bandCandidate_calibration

theorem literalGuardCalibration : PlainBlockLinearizationCodeTargets.LiteralGuardCalibration :=
  fun i r => ⟨positiveGuard_calibration i r, negativeGuard_calibration i r,
    linearizeNonnegative_calibration i r, outsideRow_calibration i r, bandCandidate_calibration i r⟩
#print axioms literalGuardCalibration

theorem residueRow_calibration (m i : Nat) (r : BlockRows.Row) :
    residueRow m i (BlockRowSubstitutionCode.rowData r) =
      BlockRowSubstitutionCode.rowData (PlainMaximumResidue.lowerRow m i r) := by
  unfold residueRow
  rw [headCoefficient_calibration, remainingOccurrences_calibration]
  rfl
#print axioms residueRow_calibration

theorem residueAtom_calibration (m i : Nat) (r : BlockRows.Row) :
    residueAtom m i (BlockRowSubstitutionCode.rowData r) =
      BlockFormulaSubstitutionCode.formulaCode (PlainMaximumResidue.lowerAtom m i r) := by
  unfold residueAtom
  rw [residueRow_calibration]
  rfl
#print axioms residueAtom_calibration

theorem literalResidueCalibration : PlainBlockLinearizationCodeTargets.LiteralResidueCalibration :=
  fun m i r => ⟨residueRow_calibration m i r, residueAtom_calibration m i r⟩
#print axioms literalResidueCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
