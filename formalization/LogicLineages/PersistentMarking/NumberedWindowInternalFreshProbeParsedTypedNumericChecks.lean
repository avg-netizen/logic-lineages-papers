module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedNumericTargets
open NumberedWindowInternalFreshProbeParsedTypedBaseProof (physicalTest baseCalibration)
open NumberedWindowInternalFreshProbeParsedEmitterNumericChecks (exact_ParsedFreshCalibration)
open NumberedWindowInternalFreshProbeDispatchProgramChecks (exact_ProbeDispatchCalibration)

theorem exact_PhysicalTypeTest : ExactPhysicalTypeTest := physicalTest

theorem exact_BaseWithResultCalibration : ExactBaseWithResultCalibration := baseCalibration

theorem exact_ParsedTypedCalibration : ExactParsedTypedCalibration := by
  intro s W valid i cal
  have a := (exact_ParsedFreshCalibration s i.scalarProg i.freshBound cal.1).2
  have h : NumberedWindowInternalFreshProbeDispatchProgram.calibrated s (chosenLeaves i) :=
    ⟨baseCalibration s i.priorTyped cal.2.1,a,cal.2.2.1,cal.2.2.2⟩
  exact ⟨a,exact_ProbeDispatchCalibration s W valid (chosenLeaves i) h⟩

#print axioms exact_PhysicalTypeTest
#print axioms exact_BaseWithResultCalibration
#print axioms exact_ParsedTypedCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
