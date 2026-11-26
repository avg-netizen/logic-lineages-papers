module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs CalibratedInputs)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseApplicationFrontendNumericChecks (exact_AllInputGuardedApplication)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)

/-- Recalibrate only the changed guarded graph, consuming the actual
selected whole-address i and unchanged packed least program. The
other original three calibration fields remain definitionally the same. -/
theorem calibrate (xs : Entries) (s : Settings) (i j : Program 1) (r d least : Program 3) (v : Inputs)
    (values : Evaluates (checks xs s) i j r d)
    (actualLeast : ActualLeastCalibration s least) (prior : CalibratedInputs s v) :
    CalibratedInputs s (frontendInputs i least v) := by
  have actualScalar : ActualScalarCalibration s i := values.1
  exact ⟨prior.1,prior.2.1,prior.2.2.1,
    exact_AllInputGuardedApplication s i least actualScalar actualLeast⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallCalibrationProof
