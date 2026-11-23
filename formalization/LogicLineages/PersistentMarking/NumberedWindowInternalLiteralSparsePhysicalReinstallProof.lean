module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalReinstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseTuple (InstalledTupleAt InstalledReportAt)
open NumberedWindowInternalSparseTupleReportProof (installed)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectTypedListInstallProof (exact_ReinstallTypedList)
open NumberedWindowInternalLiteralRefinedScalarInstallProof (exact_ReinstallLiteralRefinedScalar)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)

private theorem rebuild (xs : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i oldJ : Program 1) (oldR oldD R p₀ : Program 3) (v : Inputs)
    (prior : TupleAt xs s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (value : Reinstalled xs s i (jRaw i) R permutation) :
    TupleAt xs s W i (jRaw i) R (dCore i R permutation) v := by
  obtain ⟨_,_,_,cal,unique,_,aCal,hCal,_,shape,_⟩ := prior
  obtain ⟨evaluates,interprets,rules⟩ := value
  let d := dCore i R permutation
  have guards : InputGuards i (jRaw i) R d v.applicationGuard := by
    rw [hp]
    exact (exact_GuardRules i (jRaw i) R d p₀).1
  have total (c : Nat) : TypedProbeTotal (data i (jRaw i) R d) v.applicationGuard
      (chosenH v W) (chosenA v) c :=
    exact_SameParsedTypedProbeTotal v W closed (data i (jRaw i) R d) c
  exact ⟨evaluates,interprets,rules,cal,unique,guards,aCal,hCal,total,shape,
    fun c => carriers i (jRaw i) R d v.applicationGuard (chosenH v W) (chosenA v)
      c guards (total c)⟩

/-- Same physical address checker and parsed probe leaves, freshly installed
with actual jRaw and dCore at both its unrefined and refined even programs. -/
theorem reinstallPhysical (xs : Entries) (s : Settings) (W : List ProbeTy) (closed : ChildClosed W)
    (i oldJ cv tv : Program 1) (oldD p₀ : Program 3) (raw : Program 5) (least : Program 3)
    (v : Inputs) (prior : InstalledTupleAt xs s W i oldJ cv tv oldD p₀ raw least v) :
    let R := addressPositive cv tv raw least
    let RR := refined i R
    TupleAt xs s W i (jRaw i) R (dCore i R permutation) v ∧
    InstalledReportAt i (jRaw i) cv tv (dCore i R permutation) raw least ∧
    TupleAt xs s W i (jRaw i) RR (dCore i RR permutation) v := by
  let R := addressPositive cv tv raw least
  let RR := refined i R
  obtain ⟨tuple,guardEq,_,_⟩ := prior
  have h := tuple.1
  have base := exact_ReinstallTypedList xs s i R permutation h.1 h.2.2.1
    exact_OriginalLiteralCountFit
  have advanced := exact_ReinstallLiteralRefinedScalar xs s i R h.1 h.2.2.1
  exact ⟨rebuild xs s W closed i oldJ R oldD R p₀ v tuple guardEq base,
    installed i (jRaw i) cv tv (dCore i R permutation) raw least,
    rebuild xs s W closed i oldJ R oldD RR p₀ v tuple guardEq advanced⟩

#print axioms reinstallPhysical
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparsePhysicalReinstallProof
