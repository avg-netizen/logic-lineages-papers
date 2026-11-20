module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs CalibratedInputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets (OpenLiteralParsed)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalAtomicApplicationShapeNumericChecks (exact_OriginalShapeRefinedApplication)
open NumberedWindowInternalAtomicApplicationShapeObjectChecks (exact_OpenApplicationForgets)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets

private theorem recalibrate (s : Settings) (v : Inputs) (old : CalibratedInputs s v) :
    CalibratedInputs s (refineInputs v) :=
  ⟨old.1,old.2.1,old.2.2.1,
    exact_OriginalShapeRefinedApplication s v.applicationGuard old.2.2.2⟩

private theorem uniqueRefined (v : Inputs) (old : UniqueResult v.applicationGuard) :
    UniqueResult (refineInputs v).applicationGuard := by
  intro body α Γ f u y z first second
  exact old body α Γ f u y z
    (exact_OpenApplicationForgets v.applicationGuard body α Γ f u y first)
    (exact_OpenApplicationForgets v.applicationGuard body α Γ f u z second)

private theorem guardsRefined (i j : Program 1) (r d : Program 3) (v : Inputs)
    (old : InputGuards i j r d v.applicationGuard) :
    InputGuards i j r d (refineInputs v).applicationGuard := by
  intro c body α Γ f u y accepted
  exact old c body α Γ f u y
    (exact_OpenApplicationForgets v.applicationGuard body α Γ f u y accepted)

theorem reinstall : ExactReinstallShapeRefinedApplication := by
  intro xs s W valid i j r d v base
  obtain ⟨ev,interp,rules,cal,unique,guards⟩ := base
  let V := refineInputs v
  let S := data i j r d
  have newCal : CalibratedInputs s V := recalibrate s v cal
  have newUnique : UniqueResult V.applicationGuard := uniqueRefined v unique
  have newGuards : InputGuards i j r d V.applicationGuard := guardsRefined i j r d v guards
  obtain ⟨ha,hh⟩ := exact_ParsedTypedCalibration s W valid V newCal
  have total (c : Nat) : TypedProbeTotal S V.applicationGuard (chosenH V W) (chosenA V) c :=
    exact_SameParsedTypedProbeTotal V W valid.2.1 S c
  have shape : OpenLiteralParsed V W := exact_OpenLiteralParsedFresh V W
  exact ⟨ev,interp,rules,newCal,newUnique,newGuards,ha,hh,total,shape,
    fun c => exact_GivenFreshAlignmentAndCarriers i j r d V.applicationGuard (chosenH V W)
      (chosenA V) c newGuards (total c)⟩

theorem refineExisting : ExactRefineExistingApplicationTuple := by
  intro xs s W valid i j r d v old
  obtain ⟨ev,interp,rules,cal,unique,guards,_⟩ := old
  exact reinstall xs s W valid i j r d v ⟨ev,interp,rules,cal,unique,guards⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallProof
