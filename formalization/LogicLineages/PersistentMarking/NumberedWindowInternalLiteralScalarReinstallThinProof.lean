module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallUniqueChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof
open NumberedWindowInternalFreshProbeParsedTyped (CalibratedInputs chosenA chosenH)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationReinstallUniqueChecks (exact_UniqueGuardedApplication)
open NumberedWindowInternalSparseApplicationReinstallCalibrationProof (calibrate)
open NumberedWindowInternalSparseApplicationReinstallTargets

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)

/-- Rebuild only the original calibrated scalar and the guarded
application interface. No theorem about exchange rounds is used. -/
theorem exact_ReinstallLiteralScalar
    (xs : Entries) (s : Settings) (W : List ProbeTy) (valid : ValidWindow s W)
    (i oldI j cv tv : Program 1) (d oldCore : Program 3) (raw : Program 5)
    (least : Program 3) (v : Inputs) (scalar : ActualScalarCalibration s i)
    (old : InstalledTupleAt xs s W oldI j cv tv d oldCore raw least v) :
    let updated := frontendInputs i least v
    chosenA updated = chosenA v ∧ InstalledTupleAt xs s W i j cv tv d (applicationCore least) raw least updated := by
  let updated := frontendInputs i least v
  let R := addressPositive cv tv raw least
  let S := data i j R d
  obtain ⟨prior,_,callbacks,_⟩ := old
  obtain ⟨oldValues,_,_,oldCal,_,_,_,_,_,_,_⟩ := prior
  have values : Evaluates (checks xs s) i j R d := ⟨scalar, oldValues.2⟩
  have meaning := exact_InterpretsEvaluatingPrograms (checks xs s) i j R d values
  have newCal : CalibratedInputs s updated :=
    calibrate xs s i j R d least v values callbacks.2.2.2.1 oldCal
  have unique : UniqueResult updated.applicationGuard :=
    exact_UniqueGuardedApplication i least
  have guards : InputGuards i j R d updated.applicationGuard :=
    (exact_GuardRules i j R d (applicationCore least)).1
  obtain ⟨aCal,hCal⟩ := exact_ParsedTypedCalibration s W valid updated newCal
  have total (c : Nat) : TypedProbeTotal S updated.applicationGuard (chosenH updated W) (chosenA updated) c :=
    exact_SameParsedTypedProbeTotal updated W valid.2.1 S c
  have tuple : TupleAt xs s W i j R d updated :=
    ⟨values,meaning,⟨actualOriginalMembershipEquation S,actualOriginalCarrierExtraction S,
        actualOriginalSuccessorClosure S,actualOriginalCertifiedSuccessorClosure S,actualOriginalAccessibilityIntroduction S⟩,newCal,unique,guards,aCal,hCal,total,exact_OpenLiteralParsedFresh updated W,
      fun c => exact_GivenFreshAlignmentAndCarriers i j R d updated.applicationGuard
        (chosenH updated W) (chosenA updated) c guards (total c)⟩
  exact ⟨rfl,tuple,rfl,callbacks,NumberedWindowInternalSparseTupleReportProof.installed i j cv tv d raw least⟩

#print axioms exact_ReinstallLiteralScalar
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof
