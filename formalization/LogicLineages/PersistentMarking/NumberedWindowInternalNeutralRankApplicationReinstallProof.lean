module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallProof
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
open NumberedWindowInternalNeutralRankApplicationReinstallTargets
open NumberedWindowInternalNeutralRankGuardForgetsProof (exact_OpenRankApplicationForgets)

private theorem recalibrate (s : Settings) (i g : Program 1) (v : Inputs)
    (law : RankApplicationFit s i g v.applicationGuard) (old : CalibratedInputs s v) :
    CalibratedInputs s (selectRankInputs i g v) :=
  ⟨old.1,old.2.1,old.2.2.1,law⟩

private theorem forget (i g : Program 1) (v : Inputs) (B : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (f u y : OTerm α)
    (actual : Nonempty (Derivation B Γ (accepts (selectRankInputs i g v).applicationGuard f u y))) :
    Nonempty (Derivation B Γ (accepts v.applicationGuard f u y)) :=
  exact_OpenRankApplicationForgets i g v.applicationGuard f u y actual

private theorem uniqueSelected (i g : Program 1) (v : Inputs) (old : UniqueResult v.applicationGuard) :
    UniqueResult (selectRankInputs i g v).applicationGuard := by
  intro body α Γ f u y z first second
  exact old body α Γ f u y z (forget i g v body α Γ f u y first) (forget i g v body α Γ f u z second)

private theorem guardsSelected (i j g : Program 1) (r d : Program 3) (v : Inputs)
    (old : InputGuards i j r d v.applicationGuard) :
    InputGuards i j r d (selectRankInputs i g v).applicationGuard := by
  intro c body α Γ f u y actual
  exact old c body α Γ f u y (forget i g v body α Γ f u y actual)

/-- Reconstruct the actual same-body tuple; new typed dispatch uses
the new physical graph. Only earlier base laws and the exact supplied numeral
fits are carried over, not derivations mentioning old h. -/
theorem exact_NeutralRankApplicationReinstall : ExactNeutralRankApplicationReinstall := by
  intro xs s W valid i j g r d v law base
  obtain ⟨ev,interp,rules,cal,unique,guards⟩ := base
  let V := selectRankInputs i g v
  let S := data i j r d
  have newCal : CalibratedInputs s V := recalibrate s i g v law cal
  have newUnique : UniqueResult V.applicationGuard := uniqueSelected i g v unique
  have newGuards : InputGuards i j r d V.applicationGuard := guardsSelected i j g r d v guards
  obtain ⟨ha,hh⟩ := exact_ParsedTypedCalibration s W valid V newCal
  have total (c : Nat) : TypedProbeTotal S V.applicationGuard (chosenH V W) (chosenA V) c :=
    exact_SameParsedTypedProbeTotal V W valid.2.1 S c
  have shape : OpenLiteralParsed V W := exact_OpenLiteralParsedFresh V W
  exact ⟨rfl,ev,interp,rules,newCal,newUnique,newGuards,ha,hh,total,shape,
    fun c => exact_GivenFreshAlignmentAndCarriers i j r d V.applicationGuard (chosenH V W)
      (chosenA V) c newGuards (total c)⟩

theorem exact_NeutralRankApplicationReselect : ExactNeutralRankApplicationReselect := by
  intro xs s W valid i j g r d v law old
  obtain ⟨ev,interp,rules,cal,unique,guards,_⟩ := old
  exact exact_NeutralRankApplicationReinstall xs s W valid i j g r d v law
    ⟨ev,interp,rules,cal,unique,guards⟩

#print axioms exact_NeutralRankApplicationReinstall
#print axioms exact_NeutralRankApplicationReselect
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallProof
