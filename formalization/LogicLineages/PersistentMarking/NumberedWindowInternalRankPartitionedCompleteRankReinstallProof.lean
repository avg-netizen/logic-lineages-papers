module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedPhysicalReinstallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankedTupleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedCompleteRankReinstallProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ChildClosed ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalSparseTuple (CallbacksAt)
open NumberedWindowInternalRankPartitionedAddress (rankPartitionedAddress)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedListInstallProof (exact_ReinstallTypedList)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal FreshVariablesComputable)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)

open NumberedWindowInternalRankUniversalCarrier (completeRankEven alwaysCarried)
open NumberedWindowInternalRankUniversalCarrierNumericProof (exact_OriginalCompleteRankEvenAllInputs)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalOriginalRankedTupleProof (OriginalOutputScalar exact_OriginalRankedTuple)
open NumberedWindowInternalNeutralRankApplicationReinstallTargets (selectRankInputs)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalRankPartitionedPhysicalReinstallProof (positiveFit)

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

/-- Exact complete rank-even checker over the *rank-partitioned* physical
address program. At the same chosen i and v, assemble a fresh original
jRaw/dCore, guards and probes in its own body. No old open edge is reused. -/
theorem reinstall (entries : Entries) (s : Settings) (W : List ProbeTy)
    (closed : ChildClosed W) (i oldJ cv tv g : Program 1)
    (oldR oldD p₀ L : Program 3) (raw : Program 5) (v : Inputs)
    (prior : TupleAt entries s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (callbacks : CallbacksAt entries s cv tv raw L)
    (rankFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d) :
    let R := rankPartitionedAddress cv tv g raw L
    let N := completeRankEven i (addressRank g) R
    TupleAt entries s W i (jRaw i) N (dCore i N permutation) v := by
  let R := rankPartitionedAddress cv tv g raw L
  let N := completeRankEven i (addressRank g) R
  have scalar := prior.1.1
  have original := positiveFit entries s cv tv g raw L callbacks rankFit
  have fit : PositiveFit N (checks entries s).positive :=
    exact_OriginalCompleteRankEvenAllInputs entries s i g R scalar rankFit original
  have values := exact_ReinstallTypedList entries s i N permutation scalar fit exact_OriginalLiteralCountFit
  exact rebuild entries s W closed i oldJ oldR oldD N p₀ v prior hp values

/-- Re-choose the original ranked application on the new exact even body.
The supplied OriginalOutputScalar is the genuine all-input arithmetic
condition, not an inferred output guarantee for arbitrary settings. -/
theorem reselectRankApplication (entries : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i oldJ cv tv g : Program 1)
    (oldR oldD p₀ L : Program 3) (raw : Program 5) (v : Inputs)
    (prior : TupleAt entries s W i oldJ oldR oldD v) (hp : v.applicationGuard = guard i p₀)
    (callbacks : CallbacksAt entries s cv tv raw L)
    (rankFit : ∀ d, evaluate g (d ::ᵥ nil) = rawRank d)
    (outputScalar : OriginalOutputScalar s) :
    let R := rankPartitionedAddress cv tv g raw L
    let N := completeRankEven i (addressRank g) R
    let d := dCore i N permutation
    let next := selectRankInputs i (addressRank g) v
    chosenA next = chosenA v ∧
    next.applicationGuard = rankApplication i (addressRank g) (guard i p₀) ∧
    TupleAt entries s W i (jRaw i) N d next ∧
    ∀ c, FreshVariablesComputable (data i (jRaw i) N d)
      next.applicationGuard (chosenH next W) (chosenA next) c := by
  let R := rankPartitionedAddress cv tv g raw L
  let N := completeRankEven i (addressRank g) R
  let d := dCore i N permutation
  have scalar : ActualScalarCalibration s i := prior.1.1
  have fresh := reinstall entries s W valid.2.1 i oldJ cv tv g oldR oldD p₀ L raw v
    prior hp callbacks rankFit
  obtain ⟨same,picked,installed,freshC⟩ := exact_OriginalRankedTuple entries s W valid
    i (jRaw i) g (alwaysCarried i R) d v scalar rankFit outputScalar fresh
  exact ⟨same,picked.trans (congrArg (rankApplication i (addressRank g)) hp),installed,freshC⟩

#print axioms reinstall
#print axioms reselectRankApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedCompleteRankReinstallProof
