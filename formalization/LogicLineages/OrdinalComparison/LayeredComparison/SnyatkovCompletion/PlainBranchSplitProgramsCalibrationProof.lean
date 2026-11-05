module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupCodeProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsProof
open NormalForm (Formula)
open PlainBranchSplitPrograms

theorem small_calibration (p : Formula) : Code.small p.encode = (PlainBranchSplit.small p).encode := by
  unfold Code.small PlainBranchSplit.small
  rw [MaximalPlainBranchProgramsProof.variables_calibration,
    MaximalPlainBranchProgramsProof.cutoff_calibration, BoundedRowsCodeProof.block_calibration]

theorem smallAnswer_calibration (p : Formula) : Code.smallAnswer p.encode = PlainBranchSplit.smallAnswer p := by
  unfold Code.smallAnswer PlainBranchSplit.smallAnswer
  rw [small_calibration, ZeroValuationProof.evaluate_calibration]

theorem literalSmallCase : PlainBranchSplitProgramsTargets.LiteralSmallCase :=
  fun p => ⟨small_calibration p, smallAnswer_calibration p⟩

theorem literalBranchList : PlainBranchSplitProgramsTargets.LiteralBranchList := by
  intro p
  simp only [Code.branches, PlainBranchSplit.branches, MaximalPlainBranchProgramsProof.variables_calibration,
    MaximalPlainBranchProgramsProof.eliminate_calibration, List.map_map, Function.comp_def]

theorem literalStep : PlainBranchSplitProgramsTargets.LiteralStep := by
  intro p
  unfold Code.step PlainBranchSplit.step
  rw [PlainLinearCleanupProof.cleanup_calibration]
  dsimp only
  rw [smallAnswer_calibration, literalBranchList (PlainLinearCleanup.cleanup p)]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsProof
