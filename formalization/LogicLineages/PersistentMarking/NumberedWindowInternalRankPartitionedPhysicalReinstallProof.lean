module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedPhysicalReinstallProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ChildClosed ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalSparseAddressPositiveNumericChecks (exact_AddressPositiveComposition)
open NumberedWindowInternalRankPartitionedAddress (rankPartitionedAddress)
open NumberedWindowInternalRankPartitionedAddressNumericProof (exact_OriginalRankPartitionedAddressNumeric)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListInstallProof (exact_ReinstallTypedList)
open NumberedWindowInternalLiteralRefinedScalarInstallProof (exact_ReinstallLiteralRefinedScalar)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)

theorem positiveFit (entries : Entries) (s : Settings) (cv tv g : Program 1)
    (raw : Program 5) (L : Program 3)
    (callbacks : CallbacksAt entries s cv tv raw L)
    (rankFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d) :
    PositiveFit (rankPartitionedAddress cv tv g raw L) (checks entries s).positive := by
  obtain ⟨ctxFit,tyFit,_,_,stepFit,_,posFit⟩ := callbacks
  have original := exact_AddressPositiveComposition entries s cv tv raw L ctxFit tyFit posFit
  intro x w y
  exact (exact_OriginalRankPartitionedAddressNumeric entries s cv tv g raw L stepFit posFit
    rankFit x w y).trans (original x w y)

private theorem rebuild (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i oldJ : Program 1) (oldR oldD R p₀ : Program 3) (v : Inputs)
    (prior : TupleAt entries s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (values : Reinstalled entries s i (jRaw i) R permutation) :
    TupleAt entries s W i (jRaw i) R (dCore i R permutation) v := by
  obtain ⟨_,_,_,cal,unique,_,aCal,hCal,_,shape,_⟩ := prior
  obtain ⟨evaluates,interprets,rules⟩ := values
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

/-- Reinstall the actual rank-partitioned checker with unchanged i and p/h/a
and fresh jRaw/dCore at both the unrefined and refined even bodies. No old
open raw/least report is transported: use the physical rank-selection
branch theorem under actual reports in the newly selected body instead. -/
theorem reinstall (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i oldJ cv tv g : Program 1)
    (oldR oldD p₀ L : Program 3) (raw : Program 5) (v : Inputs)
    (prior : TupleAt entries s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (callbacks : CallbacksAt entries s cv tv raw L)
    (rankFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d) :
    let R := rankPartitionedAddress cv tv g raw L
    let RR := refined i R
    TupleAt entries s W i (jRaw i) R (dCore i R permutation) v ∧
    TupleAt entries s W i (jRaw i) RR (dCore i RR permutation) v := by
  let R := rankPartitionedAddress cv tv g raw L
  let RR := refined i R
  have scalar := prior.1.1
  have original := positiveFit entries s cv tv g raw L callbacks rankFit
  have base := exact_ReinstallTypedList entries s i R permutation scalar original exact_OriginalLiteralCountFit
  have advanced := exact_ReinstallLiteralRefinedScalar entries s i R scalar original
  exact ⟨rebuild entries s W closed i oldJ oldR oldD R p₀ v prior hp base,
    rebuild entries s W closed i oldJ oldR oldD RR p₀ v prior hp advanced⟩

#print axioms positiveFit
#print axioms reinstall
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedPhysicalReinstallProof
