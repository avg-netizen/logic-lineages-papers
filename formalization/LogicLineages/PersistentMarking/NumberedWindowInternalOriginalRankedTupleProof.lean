module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFreshProof
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankApplicationFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallProof
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankedTupleProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressApplication (graph)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankGuard (rankEven rankApplication)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)
open NumberedWindowInternalOriginalRankApplicationFitProof (exact_OriginalRankedApplicationFit)
open NumberedWindowInternalNeutralRankApplicationReinstallTargets (selectRankInputs RankApplicationFit)
open NumberedWindowInternalNeutralRankApplicationReinstallProof (exact_NeutralRankApplicationReselect)
open NumberedWindowInternalNeutralRankFreshProof (exact_RankGuardedTypedFresh)

/-- The numerical output-carrier law already verified on genuinely
closed fixed settings. It is not inferred for arbitrary Settings. -/
def OriginalOutputScalar (s : Settings) : Prop :=
  ∀ f u y, graph s f u y = true → scalar s y = true

/-- Select the actual ranked application tuple in the already chosen
physical even rank body. Both procedures use one literal original rank
program. Exact all-type fresh C is a theorem of that same tuple. -/
theorem exact_OriginalRankedTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i j raw : Program 1) (r d : Program 3) (v : Inputs)
    (cal : ActualScalarCalibration s i)
    (rawFit : ∀ n, evaluate raw (n ::ᵥ nil) = rawRank n)
    (out : OriginalOutputScalar s)
    (before : TupleAt xs s W i j (rankEven i (addressRank raw) r) d v) :
    let g := addressRank raw
    let R := rankEven i g r
    let next := selectRankInputs i g v
    chosenA next = chosenA v ∧
    next.applicationGuard = rankApplication i g v.applicationGuard ∧
    TupleAt xs s W i j R d next ∧
    ∀ c, FreshVariablesComputable (data i j R d) next.applicationGuard
      (chosenH next W) (chosenA next) c := by
  let g := addressRank raw
  let R := rankEven i g r
  let next := selectRankInputs i g v
  have oldFit := before.2.2.2.1.2.2.2
  have fit : RankApplicationFit s i g v.applicationGuard :=
    exact_OriginalRankedApplicationFit s i raw v.applicationGuard cal rawFit oldFit
      (exact_OriginalKeepsNeutralRank s) out
  obtain ⟨same,installed⟩ := exact_NeutralRankApplicationReselect xs s W valid i j g R d v fit before
  exact ⟨same,rfl,installed,fun c =>
    exact_RankGuardedTypedFresh xs s W i j raw r d v.applicationGuard next c installed rfl⟩

#print axioms exact_OriginalRankedTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankedTupleProof
