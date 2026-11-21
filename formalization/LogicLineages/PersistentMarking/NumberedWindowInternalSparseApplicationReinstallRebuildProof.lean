module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallUniqueChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallRebuildProof
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

/-- On this exact same physical data/body, rebuild the dependent tuple
at the literal new application leaf. No old application, chosen-H
or alignment derivation is transported. -/
theorem reinstall : ExactReinstallGuardedApplicationTuple := by
  intro xs s W valid i j cv tv d oldCore raw least v old
  let updated := frontendInputs i least v
  let R := addressPositive cv tv raw least
  let S := data i j R d
  obtain ⟨prior,_,callbacks,report⟩ := old
  obtain ⟨values,meaning,rules,oldCal,_,_,_,_,_,_,_⟩ := prior
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
    ⟨values,meaning,rules,newCal,unique,guards,aCal,hCal,total,exact_OpenLiteralParsedFresh updated W,
      fun c => exact_GivenFreshAlignmentAndCarriers i j R d updated.applicationGuard
        (chosenH updated W) (chosenA updated) c guards (total c)⟩
  exact ⟨rfl,tuple,rfl,callbacks,report⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallRebuildProof
