module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeLowerCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode

theorem literalEliminationCalibration : TiedLinearCodeTargets.LiteralEliminationCalibration := by
  intro x p
  dsimp only [eliminate, TiedLinear.eliminate]
  rw [literalTokenCalibration p, literalLiftCalibration (TiedLinear.tokens p) x p,
    LinearRowsCodeProof.eliminate_calibration,
    literalLowerCalibration (TiedLinear.tokens p) x (LinearRows.eliminate 0 (TiedLinear.liftFormula (TiedLinear.tokens p) x p))]
#print axioms literalEliminationCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
