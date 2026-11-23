module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankFreshProof
import LogicLineages.PersistentMarking.NumberedWindowInternalRankUniversalCarrierObjectProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothUnrankedPullbackProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPullbackTargets (Pullback)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalRankUniversalCarrier (completeRankEven alwaysCarried)
open NumberedWindowInternalNeutralRankGuardDropProof (exact_OpenRankGuardDrop)
open NumberedWindowInternalNeutralBothUnrankedPullbackTargets (BothUnrankedForwardRule)
open NumberedWindowInternalNeutralBothUnrankedPullbackProof (exact_InternalBothUnrankedPullback)
open NumberedWindowInternalRankUniversalCarrierObjectProof (exact_OpenCompleteRankEdgeCarrier)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralRankFreshProof (exact_RankGuardedTypedFresh)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowInternalProbeChecks (exact_TypedComputabilityImpliesMembership)
open NumberedWindowComputabilityFormulaTargets (formula)

theorem exact_CompleteRankBothUnrankedPullback (i j g : Program 1) (r d p : Program 3) (c : Nat)
    (guards : InputGuards i j (completeRankEven i g r) d (rankApplication i g p))
    (forward : BothUnrankedForwardRule
      (data i j (completeRankEven i g r) d) g (rankApplication i g p) c) :
    Pullback (data i j (completeRankEven i g r) d) (rankApplication i g p) c :=
  exact_InternalBothUnrankedPullback i j g (completeRankEven i g r) d (rankApplication i g p) c
    guards (exact_OpenRankGuardDrop i j g (alwaysCarried i r) d c)
    (exact_OpenCompleteRankEdgeCarrier i j g r d c) forward

/-- All original finite source types on the actual installed tuple. Only
true same-program forwarding along zero/zero original edges remains. -/
theorem exact_CompleteRankBothUnrankedTypedComputability
    (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j raw : Program 1) (r d p : Program 3) (c : Nat) (v : Inputs)
    (pdef : v.applicationGuard = rankApplication i (addressRank raw) p)
    (pack : TupleAt xs s W i j (completeRankEven i (addressRank raw) r) d v)
    (forward : BothUnrankedForwardRule
      (data i j (completeRankEven i (addressRank raw) r) d) (addressRank raw) v.applicationGuard c)
    (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α)
    (typed : Nonempty (Derivation (sourceBody (data i j (completeRankEven i (addressRank raw) r) d) c) Γ
      (typedAt (chosenH v W) τ q)))
    (computable : Nonempty (Derivation (sourceBody (data i j (completeRankEven i (addressRank raw) r) d) c) Γ
      (formula v.applicationGuard τ q))) :
    Nonempty (Derivation (sourceBody (data i j (completeRankEven i (addressRank raw) r) d) c) Γ
      (membership false q)) := by
  let g := addressRank raw
  let R := completeRankEven i g r
  let S := data i j R d
  have guards : InputGuards i j R d v.applicationGuard := pack.2.2.2.2.2.1
  have total := pack.2.2.2.2.2.2.2.2.1
  have pSame : v.applicationGuard = rankApplication i g p := pdef
  have pull : Pullback S v.applicationGuard c := by
    rw [pSame] at guards forward ⊢
    exact exact_CompleteRankBothUnrankedPullback i j g r d p c guards forward
  exact exact_TypedComputabilityImpliesMembership S v.applicationGuard (chosenH v W)
    (chosenA v) c pull (total c) (exact_RankGuardedTypedFresh xs s W i j raw (alwaysCarried i r) d p v c pack pdef)
    τ α Γ q typed computable

#print axioms exact_CompleteRankBothUnrankedPullback
#print axioms exact_CompleteRankBothUnrankedTypedComputability
end LogicLineages.PersistentMarking.NumberedWindowInternalCompleteRankBothUnrankedPullbackProof
