module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxSkeletonProof
import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTraceProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsProof
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchProof
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchSupportProof
import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorProof
import LogicLineages.PermittedControl.ActualTraceSignCutoffProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open OrdinalComparison FieldComparison PreparedProjection
open ActualRankedNormalizationSyntax (extend normalizedTerms exactNormalizedTermSkeleton)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualFiniteGlobalTail (syntaxOf)
open ActualReadChargeIteration (stateValue ActiveAt NodeGuards)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (exactNormalizedReads)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualFiniteSignedNodeBranch (nodeLabels nodePacket StaticActive StaticGuards NodeResult
  exactFiniteSignedNodeBranch readTransport matchedTransport nodeCoefficient)
open ActualFiniteFullValueGuards (ReadyFamily PaidFamily exactFiniteFullValueGuards)
open ActualGlobalComparisonCeiling (exactCombinedReachedComparisonSupply)
open ActualSymbolicZeroSuccessor (exactActualSymbolicZeroSuccessor)
open ActualTraceSignCutoff (exactReachedCutoffDominance)
open ActualMixedRowLeadingSum (rowCutoffCode)
open MixedSameRankResidue (encodeWeighted)
open SignedRowGuardedTest (Test)

private theorem sameTest (R coef : Int) (coefNZ : coef ≠ 0)
    (sign : (0 < R ↔ 0 < coef) ∧ (R < 0 ↔ coef < 0) ∧ (0 ≤ R ↔ 0 < coef) ∧ R ≠ 0)
    (test : OrderTest) (positive : Bool) :
    test.test.atPolarity positive R ↔ test.test.atPolarity positive coef := by
  have actual : test.test.Holds R ↔ test.test.Holds coef := by
    cases test with
    | equalZero =>
        exact ⟨fun impossible => False.elim (sign.2.2.2 impossible),
          fun impossible => False.elim (coefNZ impossible)⟩
    | nonnegative =>
        exact sign.2.2.1.trans (by omega)
    | positive => exact sign.1
  cases positive with
  | false => exact not_congr actual
  | true => exact actual

theorem exactReachedNonlinearRoute : ExactReachedNonlinearRoute := by
  intro f B baseline r top z initial ctx n s path active
  let θ := extend baseline top z
  let raw := syntaxOf s
  have rootReady := contextExtension ctx
  have below := contextBelow baseline top z
  obtain ⟨live,ranks⟩ := reachedLiveAndRank path (sourceLive ctx) ctx.ranks
  have scope : ∀ t ∈ raw, t.2.rank < r ∧ t.2.rank ≤ top := by
    intro t h
    obtain ⟨rd,atSource,rfl⟩ := List.mem_map.mp h
    exact ranks rd atSource
  obtain ⟨xs,normal,_,_,_,_,_⟩ := (exactNormalizedReads f θ s.reads).2 live
  have frames : xs.map Prod.fst = normalizedTerms raw := exactNormalizedTermSkeleton.1 _ _ _ _ normal
  have activeAt : ActiveAt top xs := by
    simpa only [ActiveAt,StaticActive,frames] using active
  obtain ⟨current,ready,paid⟩ := exactCombinedReachedComparisonSupply f B ctx.chosen θ baseline
    r top n initial s rootReady.1 below (sourceLive ctx) ctx.long (initialScope ctx)
    (paidTransfer ctx) (paidComparison ctx) path xs normal activeAt
  have guards : StaticGuards B θ raw := by simpa only [NodeGuards,StaticGuards,frames] using current
  have readyHere : ReadyFamily B baseline top (nodeLabels raw) := by
    simpa only [nodeLabels,frames] using ready
  have paidHere : PaidFamily B baseline top z (nodeLabels raw) := by
    simpa only [nodeLabels,frames,rootReady.2.1] using paid
  have available := exactFiniteFullValueGuards f B ctx.chosen baseline top (nodeLabels raw) readyHere
  have rawLive : liftedReads f (Function.update baseline top z) s.reads :=
    (readTransport f θ (Function.update baseline top z) top rootReady.2.2
      s.reads (fun rd h => (ranks rd h).2)).mp live
  refine ⟨?_,?_⟩
  · obtain ⟨a,member,_,ν,tied,passes⟩ := available.2 z paidHere
    exact ⟨a,member,ν,tied,passes⟩
  · intro a member passing
    obtain ⟨ν,tied,accepts⟩ := passing
    have actual := (exactFiniteSignedNodeBranch f B ctx.chosen baseline r top s.constant raw
      ctx.lower scope active readyHere a member).2.2 ν tied z ctx.above paidHere guards
      s.reads rfl rawLive accepts
    have rawMatch := ((available.1 a member).2.2 ν tied z paidHere).mp accepts
    have matchHere := (matchedTransport f θ (Function.update baseline top z) top rootReady.2.2
      (nodeLabels raw) (fun l used => (readyHere.1 l used).1) a).mpr rawMatch
    have actualResult : NodeResult f B θ r top z s raw a := by
      cases s <;> exact actual
    rcases actualResult with ⟨zero,out,edge⟩ | ⟨nonzero,_,signed⟩
    · exact Or.inl ⟨zero,out,edge,exactActualSymbolicZeroSuccessor f B ctx.chosen θ r top
        s out raw a rfl edge matchHere⟩
    · have origin := (exactReachedCutoffDominance f B θ r top n initial s path xs normal).2
      have now : rowCutoffCode s.constant ((normalizedTerms raw).map encodeWeighted) ≤ z := by
        rw [← frames]
        exact origin.trans ctx.signTail
      exact Or.inr ⟨nonzero,fun test positive =>
        sameTest (stateValue s) (nodeCoefficient raw a) nonzero (signed now) test positive⟩

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
