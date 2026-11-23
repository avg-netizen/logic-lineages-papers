module

public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (OTerm TypedProbeTotal)
open NumberedWindowAddressApplication (graph)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs CalibratedInputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets (OpenLiteralParsed)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalAtomicApplicationShapeNumericChecks (exact_OriginalShapeRefinedApplication)
open NumberedWindowInternalAtomicApplicationShapeObjectChecks (exact_OpenApplicationForgets)
open NumberedWindowInternalApplicationOutputGuardNumericProof (exact_ApplicationOutputGuardCalibration)
open NumberedWindowInternalApplicationOutputGuardOpenProof (exact_OpenApplicationOutputGuard)
open NumberedWindowInternalApplicationOutputGuardReinstallTargets

private theorem recalibrate (s : Settings) (i : Program 1) (v : Inputs)
    (law : OutputScalarLaw s i) (old : CalibratedInputs s v) :
    CalibratedInputs s (selectOutputInputs i v) := by
  have shaped := exact_OriginalShapeRefinedApplication s v.applicationGuard old.2.2.2
  have installed := exact_ApplicationOutputGuardCalibration i
    (refinedApplication v.applicationGuard) (graph s) shaped law
  exact ⟨old.1,old.2.1,old.2.2.1,installed⟩

private theorem forget (i : Program 1) (v : Inputs) (B : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (f u y : OTerm α)
    (actual : Nonempty (Derivation B Γ (accepts (selectOutputInputs i v).applicationGuard f u y))) :
    Nonempty (Derivation B Γ (accepts v.applicationGuard f u y)) :=
  exact_OpenApplicationForgets v.applicationGuard B α Γ f u y
    (exact_OpenApplicationOutputGuard i (refinedApplication v.applicationGuard) B α Γ f u y actual).1

private theorem uniqueSelected (i : Program 1) (v : Inputs) (old : UniqueResult v.applicationGuard) :
    UniqueResult (selectOutputInputs i v).applicationGuard := by
  intro body α Γ f u y z first second
  exact old body α Γ f u y z (forget i v body α Γ f u y first) (forget i v body α Γ f u z second)

private theorem guardsSelected (i j : Program 1) (r d : Program 3) (v : Inputs)
    (old : InputGuards i j r d v.applicationGuard) :
    InputGuards i j r d (selectOutputInputs i v).applicationGuard := by
  intro c body α Γ f u y actual
  exact old c body α Γ f u y (forget i v body α Γ f u y actual)

/-- Reconstruct the actual same-body tuple; new typed dispatch uses
the new physical graph. Only earlier base laws and trusted same-numeral
fits are carried over, not derivations mentioning old h. -/
theorem exact_ApplicationOutputGuardReinstall : ExactApplicationOutputGuardReinstall := by
  intro xs s W valid i j r d v law base
  obtain ⟨ev,interp,rules,cal,unique,guards⟩ := base
  let V := selectOutputInputs i v
  let S := data i j r d
  have newCal : CalibratedInputs s V := recalibrate s i v law cal
  have newUnique : UniqueResult V.applicationGuard := uniqueSelected i v unique
  have newGuards : InputGuards i j r d V.applicationGuard := guardsSelected i j r d v guards
  obtain ⟨ha,hh⟩ := exact_ParsedTypedCalibration s W valid V newCal
  have total (c : Nat) : TypedProbeTotal S V.applicationGuard (chosenH V W) (chosenA V) c :=
    exact_SameParsedTypedProbeTotal V W valid.2.1 S c
  have shape : OpenLiteralParsed V W := exact_OpenLiteralParsedFresh V W
  exact ⟨rfl,ev,interp,rules,newCal,newUnique,newGuards,ha,hh,total,shape,
    fun c => exact_GivenFreshAlignmentAndCarriers i j r d V.applicationGuard (chosenH V W)
      (chosenA V) c newGuards (total c)⟩

theorem exact_ApplicationOutputGuardReselect : ExactApplicationOutputGuardReselect := by
  intro xs s W valid i j r d v law old
  obtain ⟨ev,interp,rules,cal,unique,guards,_⟩ := old
  exact exact_ApplicationOutputGuardReinstall xs s W valid i j r d v law
    ⟨ev,interp,rules,cal,unique,guards⟩

#print axioms exact_ApplicationOutputGuardReinstall
#print axioms exact_ApplicationOutputGuardReselect
end LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallProof
