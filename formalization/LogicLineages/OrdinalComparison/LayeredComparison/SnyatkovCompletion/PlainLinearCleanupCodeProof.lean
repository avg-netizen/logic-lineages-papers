module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDataProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
open NormalForm (Formula)
open PlainLinearCleanup
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem linearNames_calibration (p : Formula) : Code.linearNames p.encode = linearNames p := by
  simp only [Code.linearNames, linearNames, MaximalPlainBranchProgramsProof.variables_calibration,
    LinearRowsCodeProof.isLinear_calibration]

theorem cleanup_calibration (p : Formula) : Code.cleanup p.encode = (cleanup p).encode := by
  unfold Code.cleanup cleanup
  rw [linearNames_calibration, LinearBlockProof.eliminate_calibration]

theorem literalCodeCalibration : PlainLinearCleanupTargets.LiteralCodeCalibration :=
  fun p => ⟨linearNames_calibration p, cleanup_calibration p⟩

attribute [local irreducible] LinearRows.Code.isLinear MaximalPlainBranchPrograms.Code.variables

theorem linearNames_primitive : Primrec Code.linearNames := by
  have hp : Primrec₂ (fun code i : Nat => LinearRows.Code.isLinear i code) :=
    LinearRowsCodeProof.isLinear_primitive.comp Primrec.snd Primrec.fst
  exact (InactivePhiProgramsProof.filterWith_primitive hp).comp Primrec.id
    MaximalPlainBranchProgramsProof.variables_primitive

attribute [local irreducible] Code.linearNames

theorem cleanup_primitive : Primrec Code.cleanup :=
  LinearBlockProof.eliminate_primitive.comp linearNames_primitive Primrec.id

theorem actualNumericPrograms : PlainLinearCleanupTargets.ActualNumericPrograms :=
  ⟨linearNames_primitive, cleanup_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
