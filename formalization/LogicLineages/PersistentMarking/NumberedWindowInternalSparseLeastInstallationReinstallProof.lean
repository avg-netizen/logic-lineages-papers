module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationReinstallProof
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH chosenA)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseTuplePresentationProof (rebuild)
open NumberedWindowInternalSparseTupleReportProof (installed)
open NumberedWindowInternalSparsePathAdvanceNumericChecks (exact_AdvanceComposition)
open NumberedWindowInternalSparsePositiveFoldNumericChecks (exact_FoldComposition)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_AddressPositiveComposition)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalSparseLeastInstallationTargets

theorem reinstall : ExactReinstallCalibratedLeast := by
  intro entries s W valid i j cv tv d p₀ raw oldLeast newLeast v old newCal
  let R := addressPositive cv tv raw newLeast
  let S := data i j R d
  obtain ⟨oldTuple,guardEq,oldCallbacks,_⟩ := old
  obtain ⟨oldValues,_,_,inputCal,unique,_,aCal,hCal,_,openShape,_⟩ := oldTuple
  obtain ⟨ctxCal,typeCal,rawCal,_,_,_,_⟩ := oldCallbacks
  have advance := exact_AdvanceComposition entries s raw newLeast rawCal newCal
  obtain ⟨fuel,positive⟩ := exact_FoldComposition entries s raw newLeast advance
  have newCallbacks : CallbacksAt entries s cv tv raw newLeast :=
    ⟨ctxCal,typeCal,rawCal,newCal,advance,fuel,positive⟩
  have addressValue := exact_AddressPositiveComposition entries s cv tv raw newLeast
    ctxCal typeCal positive
  have branchValues : Evaluates (checks entries s) i j R d :=
    ⟨oldValues.1,oldValues.2.1,addressValue,oldValues.2.2.2⟩
  obtain ⟨values,meaning,rules⟩ := rebuild entries s i j R d branchValues
  have guards : InputGuards i j R d v.applicationGuard := by
    rw [guardEq]
    exact (exact_GuardRules i j R d p₀).1
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W valid.2.1 S c
  have newTuple : TupleAt entries s W i j R d v :=
    ⟨values,meaning,rules,inputCal,unique,guards,aCal,hCal,total,openShape,
      fun c => exact_GivenFreshAlignmentAndCarriers i j R d v.applicationGuard
        (chosenH v W) (chosenA v) c guards (total c)⟩
  exact ⟨newTuple,guardEq,newCallbacks,installed i j cv tv d raw newLeast⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationReinstallProof
