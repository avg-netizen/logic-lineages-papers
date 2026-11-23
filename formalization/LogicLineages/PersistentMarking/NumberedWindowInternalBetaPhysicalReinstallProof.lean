module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaPositiveCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaPhysicalReinstallProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalBetaSub (betaChecker Fits run2)
open NumberedWindowInternalBetaRootDispatch (root')
open NumberedWindowInternalBetaCheckerFitProof (guardSpec argSpec bodySpec)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
  (ActualAddressPositiveCalibration ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseTuple (CallbacksAt InstalledTupleAt InstalledReportAt)
open NumberedWindowInternalSparseTuplePresentationProof (rebuild)
open NumberedWindowInternalSparseTupleReportProof (installed)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalLiteralSparsePhysicalReinstallProof (reinstallPhysical)

private theorem rebuildChangedRaw (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i j cv tv : Program 1) (old d p₀ least : Program 3)
    (raw : Program 5) (v : Inputs) (prior : TupleAt entries s W i j old d v)
    (guardEq : v.applicationGuard = guard i p₀)
    (cal : ActualAddressPositiveCalibration entries s cv tv raw least)
    (callbacks : CallbacksAt entries s cv tv raw least) :
    InstalledTupleAt entries s W i j cv tv d p₀ raw least v := by
  let R := addressPositive cv tv raw least
  let S := data i j R d
  obtain ⟨oldValues,_,_,inputCal,unique,_,aCal,hCal,_,shape,_⟩ := prior
  have values : Evaluates (checks entries s) i j R d :=
    ⟨oldValues.1,oldValues.2.1,cal,oldValues.2.2.2⟩
  obtain ⟨values,meaning,rules⟩ := rebuild entries s i j R d values
  have guards : InputGuards i j R d v.applicationGuard := by
    rw [guardEq]
    exact (exact_GuardRules i j R d p₀).1
  have total (c : Nat) : TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W closed S c
  have tuple : TupleAt entries s W i j R d v :=
    ⟨values,meaning,rules,inputCal,unique,guards,aCal,hCal,total,shape,
      fun c => exact_GivenFreshAlignmentAndCarriers i j R d v.applicationGuard
        (chosenH v W) (chosenA v) c guards (total c)⟩
  exact ⟨tuple,guardEq,callbacks,installed i j cv tv d raw least⟩

/-- Freshly build the actual unrefined and refined source bodies with the
conservatively replaced β root. The already chosen i and physical p/h/a
data v are unchanged, and jRaw/dCore are rebuilt over the new exact r. No
open derivation about the old body is used as a derivation about the new one. -/
theorem selected (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i j cv tv syntaxProg : Program 1)
    (oldR oldD p₀ original other windowProg least : Program 3) (v : Inputs)
    (prior : TupleAt entries s W i j oldR oldD v)
    (guardEq : v.applicationGuard = guard i p₀)
    (old : ActualRoot (NumberedWindowConcreteCheckers.root entries s) original)
    (fallback : ActualFallback other)
    (syntaxFit : ActualRawSyntax syntaxProg) (windowFit : ActualPackedWindow s windowProg)
    (ctxFit : ActualContextGuard cv) (tyFit : ActualTypeGuard tv)
    (leastFit : ActualLeastCalibration s least) :
    ∃ guardProg arg body sub : Program 2,
      Fits sub ∧
      (∀ src dst, run2 guardProg src dst = guardSpec src dst) ∧
      (∀ src dst, run2 arg src dst = argSpec src) ∧
      (∀ src dst, run2 body src dst = bodySpec src) ∧
      let root := root' original (betaChecker guardProg arg body sub)
      let raw := typedRaw5 root other windowProg syntaxProg
      let R := addressPositive cv tv raw least
      let RR := refined i R
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
      CallbacksAt entries s cv tv raw least ∧
      TupleAt entries s W i (jRaw i) R (dCore i R permutation) v ∧
      InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
      TupleAt entries s W i (jRaw i) RR (dCore i RR permutation) v := by
  obtain ⟨g,a,b,sub,hsub,hg,ha,hb,rootFit,callbacks,cal⟩ :=
    NumberedWindowInternalBetaPositiveCalibrationProof.selected entries s cv tv syntaxProg
      original other windowProg least old fallback syntaxFit windowFit ctxFit tyFit leastFit
  let raw := typedRaw5 (root' original (betaChecker g a b sub)) other windowProg syntaxProg
  have installedTuple := rebuildChangedRaw entries s W closed i j cv tv oldR oldD p₀ least
    raw v prior guardEq cal callbacks
  exact ⟨g,a,b,sub,hsub,hg,ha,hb,rootFit,callbacks,
    reinstallPhysical entries s W closed i j cv tv oldD p₀ raw least v installedTuple⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaPhysicalReinstallProof
