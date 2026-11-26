module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeRenameCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode

theorem small_calibration (bound : List Nat) (p : BlockRows.Formula) :
    small bound (BlockFormulaSubstitutionCode.formulaCode p) =
      (PlainBlockSplit.small bound p).map stateData := by
  cases bound with
  | nil => rfl
  | cons i rest =>
      simp only [small, PlainBlockSplit.small, PlainBlockLinearizationCodeProof.cutoff_calibration,
        List.map_map, Function.comp_def, stateData]
      apply List.map_congr_left
      intro n hn
      apply congrArg (fun code : Nat => ((i :: rest).erase i, code))
      exact BlockFormulaSubstitutionCodeProof.literalFormulaCalibration i (.numeral n) p
#print axioms small_calibration

theorem ties_calibration (bound : List Nat) (p : BlockRows.Formula) :
    ties bound (BlockFormulaSubstitutionCode.formulaCode p) =
      (PlainBlockSplit.ties bound p).map stateData := by
  simp only [ties, PlainBlockSplit.ties, List.map_flatMap, List.map_map,
    Function.comp_def, stateData, rename_calibration]
#print axioms ties_calibration

theorem bands_calibration (bound : List Nat) (p : BlockRows.Formula) :
    bands bound (BlockFormulaSubstitutionCode.formulaCode p) =
      (PlainBlockSplit.bands bound p).map stateData := by
  unfold bands PlainBlockSplit.bands
  rw [PlainBlockLinearizationCodeProof.atoms_calibration, List.map_flatMap]
  apply congrArg (fun f : Nat → List StateData => bound.flatMap f)
  funext i
  rw [List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f : BlockRows.Atom → List StateData => (PlainBlockSplit.atoms p).flatMap f)
  funext a
  simp only [Function.comp_def, BlockFormulaSubstitutionCodeProof.decode_atomData]
  cases a with
  | nonnegative r =>
      simp only [BlockFormulaSubstitutionCode.atomData, Nat.reduceEqDiff, reduceIte,
        PlainBlockLinearizationCodeProof.headCoefficient_calibration]
      split_ifs
      · rfl
      · rw [List.map_map]
        apply List.map_congr_left
        intro d hd
        change (_, BlockFormulaSubstitutionCode.formula i
          (PlainBlockLinearizationCode.bandCandidate i (BlockRowSubstitutionCode.rowData r) d)
          (BlockFormulaSubstitutionCode.formulaCode p)) =
            (_, BlockFormulaSubstitutionCode.formulaCode (p.substitute i (PlainBlockSplit.bandCandidate i r d)))
        apply congrArg (fun code : Nat => (bound.erase i, code))
        rw [PlainBlockLinearizationCodeProof.bandCandidate_calibration]
        exact BlockFormulaSubstitutionCodeProof.literalFormulaCalibration i (PlainBlockSplit.bandCandidate i r d) p
  | divisible m r =>
      simp only [BlockFormulaSubstitutionCode.atomData, Nat.reduceEqDiff, reduceIte, List.map_nil]
#print axioms bands_calibration

theorem far_calibration (bound : List Nat) (p : BlockRows.Formula) :
    far bound (BlockFormulaSubstitutionCode.formulaCode p) =
      (PlainBlockSplit.far bound p).map stateData := by
  simp only [far, PlainBlockSplit.far, List.map_map, Function.comp_def, stateData]
  apply List.map_congr_left
  intro i hi
  apply congrArg (fun code : Nat => (bound.erase i, code))
  rw [PlainBlockLinearizationCodeProof.frame_calibration,
    PlainBlockLinearizationCodeProof.outside_calibration, PlainBlockLinearizationCodeProof.linearize_calibration]
  exact TiedLinearCodeProof.literalEliminationCalibration i
    (.conjunction (PlainBlockSplit.frame bound i p)
      (.conjunction (PlainBlockSplit.outside i p) (PlainBlockSplit.linearize i p)))
#print axioms far_calibration

theorem literalBranchFamiliesCalibration : PlainBlockDispatchCodeTargets.LiteralBranchFamiliesCalibration := fun bound p => ⟨small_calibration bound p, ties_calibration bound p,
    bands_calibration bound p, far_calibration bound p⟩
#print axioms literalBranchFamiliesCalibration

theorem literalBranchAssemblyCalibration : PlainBlockDispatchCodeTargets.LiteralBranchAssemblyCalibration := by
  intro bound p
  simp only [branches, PlainBlockSplit.branches, List.map_append,
    small_calibration, ties_calibration, bands_calibration, far_calibration]
#print axioms literalBranchAssemblyCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
