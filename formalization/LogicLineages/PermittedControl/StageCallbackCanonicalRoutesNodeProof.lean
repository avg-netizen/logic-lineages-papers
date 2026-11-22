module
public import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesTargets
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesLayoutProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof
import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchSupportProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalNodeProgressProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof
import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTruthProof
import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthInactiveProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (exactNormalizedReads)
open ActualCanonicalOperandGrouping (groupTyped normalizeCanonical exactCanonicalReads)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket exactCanonicalInactiveTruth)
open ActualCanonicalZeroTrace (CanonicalTrace CanonicalZeroWitness exactCanonicalZeroReplay
  exactCanonicalTraceReplay)
open ActualCanonicalReachedFunding (exactCanonicalReachFacts exactCanonicalReachedFunding)
open ActualCanonicalNodeProgress (NonlinearOutcome exactCanonicalReachedProgress)
open ActualCanonicalStoppingTrace (StopsAt)
open ActualCanonicalFundedTerminal (exactFundedForwardTruth)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Pair Answer)
open ActualFiniteFullValueGuards (pairs patterns compile Matches exactFiniteFullValueGuards)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualFiniteSignedNodeBranch (matchedTransport)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (PacketHolds RouteHolds)
open ActualBoundedSignedRouteSemantics (RunContext stateSyntax contextExtension contextBelow
  sourceLive paidTransfer paidComparison tiedBelow)
open ActualRankedNormalizationSyntax (extend)
open ActualReadChargeIteration (ReadState RankBound ActiveAt stateValue stateCharge)
open ActualFiniteGlobalTail (syntaxOf)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)

/-- Lifted reads have a canonical normalization whose term column is the
first-occurrence grouping of the literal term column. -/
theorem canonicalNormal (f ρ : Nat → Nat) (raw : List Read) (live : liftedReads f ρ raw) :
    ∃ xs, normalizeCanonical f ρ raw = some xs ∧
      xs.map Prod.fst = groupTyped (raw.map Prod.fst) := by
  obtain ⟨old,oldCode,_⟩ := (exactNormalizedReads f ρ raw).2 live
  obtain ⟨out,outCode,_,frames,_⟩ := (exactCanonicalReads f ρ raw).2 old oldCode
  exact ⟨out,outCode,frames⟩

theorem canonicalFrames (f ρ : Nat → Nat) (raw xs : List Read) (live : liftedReads f ρ raw)
    (normal : normalizeCanonical f ρ raw = some xs) :
    xs.map Prod.fst = groupTyped (raw.map Prod.fst) := by
  obtain ⟨out,outCode,frames⟩ := canonicalNormal f ρ raw live
  have same : xs = out := Option.some.inj (normal.symm.trans outCode)
  rw [same]
  exact frames

theorem reached {f : Nat → Nat} {B : Nat} {baseline : Nat → Nat} {r top z : Nat}
    {initial : ReadState} (ctx : CanonicalContext f B baseline r top z initial)
    {answers : List (List Answer)} {s : ReadState}
    (path : CanonicalTrace f B (extend baseline top z) r top answers initial s) :
    liftedReads f (extend baseline top z) s.reads ∧ RankBound r top s ∧
      stateValue initial = stateValue s := by
  obtain ⟨live,ranks,_⟩ := exactCanonicalReachFacts f B ctx.run.chosen (extend baseline top z)
    r top initial s answers (sourceLive ctx.run) ctx.run.ranks ctx.run.long path
  obtain ⟨_,_,_,_,value,_⟩ := exactCanonicalTraceReplay f B ctx.run.chosen
    (extend baseline top z) r top initial s answers path
  exact ⟨live,ranks,value⟩

theorem exactCanonicalReachedLinear : ExactCanonicalReachedLinear := by
  intro f B baseline r top z initial ctx answers s path idle test positive
  let q := canonicalPacket top s.constant (syntaxOf s) test.test positive
  obtain ⟨live,ranks,_⟩ := reached ctx path
  obtain ⟨xs,normal,frames⟩ := canonicalNormal f (extend baseline top z) s.reads live
  have inactive : ¬ ActiveAt top xs := by
    intro activeAt
    apply idle
    obtain ⟨t,member,facts⟩ := activeAt
    rw [frames] at member
    exact ⟨t,member,facts⟩
  have admitted : test.test.Admitted := by cases test <;> trivial
  obtain ⟨_,supplies,checks⟩ := exactCanonicalInactiveTruth f (extend baseline top z) top
    s.constant s.reads xs live (fun rd used => (ranks rd used).2) normal inactive
    test.test positive admitted
  have topValue : extend baseline top z top = z := (contextExtension ctx.run).2.1
  have fit (ν : Nat → Nat) :
      PreparedTableTied f top baseline q.1 ν ↔
        PreparedTableTied f top (extend baseline top z) q.1 ν :=
    tiedBelow f baseline (extend baseline top z) top q.1 ν (contextBelow baseline top z)
  have real (ν : Nat → Nat) (tied : PreparedTableTied f top (extend baseline top z) q.1 ν) :
      q.2.eval (Function.update ν 0 z) ↔ test.test.atPolarity positive (stateValue s) := by
    have actual := (checks ν tied).2.2.1
    rw [topValue] at actual
    exact actual
  constructor
  · rintro ⟨_,ν,tied,passes⟩
    exact (real ν ((fit ν).mp tied)).mp passes
  · intro valid
    obtain ⟨ν,tied⟩ := supplies
    exact ⟨fun g used => False.elim (List.not_mem_nil used),
      ν,(fit ν).mpr tied,(real ν tied).mpr valid⟩

theorem exactCanonicalReachedGuards : ExactCanonicalReachedGuards := by
  intro f B baseline r top z initial ctx answers s path active
  have rootReady := contextExtension ctx.run
  have below := contextBelow baseline top z
  have chosen := ctx.run.chosen
  have atTop : extend baseline top z top = z := rootReady.2.1
  obtain ⟨live,ranks,valueEq⟩ := reached ctx path
  obtain ⟨xs,normal,xsLive,branches⟩ := exactCanonicalReachedProgress f B chosen
    (extend baseline top z) rootReady.1 r top initial s answers (sourceLive ctx.run)
    ctx.run.ranks ctx.run.long (paidTransfer ctx.run) (paidComparison ctx.run) path
  have frames : xs.map Prod.fst = groupTyped (syntaxOf s) :=
    canonicalFrames f (extend baseline top z) s.reads xs live normal
  have activeAt : ActiveAt top xs := by
    obtain ⟨t,member,facts⟩ := active
    rw [← frames] at member
    exact ⟨t,member,facts⟩
  obtain ⟨_,ready,paid⟩ := exactCanonicalReachedFunding f B chosen (extend baseline top z)
    baseline r top initial s answers rootReady.1 below (sourceLive ctx.run) ctx.run.ranks
    ctx.run.long (paidTransfer ctx.run) (paidComparison ctx.run) path xs normal activeAt
  rw [frames] at ready
  rw [frames,atTop] at paid
  have outcome : NonlinearOutcome f B (extend baseline top z) r top s xs := by
    rcases branches with idle | ⟨_,result⟩
    · exact False.elim (idle activeAt)
    · exact result
  obtain ⟨a₀,anns,C,ν₀,listed,matched,tiedAccept,aligned,maximum,floor,nodeGuards,ready₀,
    transfer,coefEq,verdict⟩ := outcome
  have stopIf : maximalCoefficient (xs.map Prod.fst) a₀ ≠ 0 →
      StopsAt f B (extend baseline top z) r top s := by
    intro nonzero
    rcases verdict with ⟨_,equation⟩ | ⟨zero,_⟩
    · exact ⟨xs,normal,xsLive,Or.inr ⟨activeAt,a₀,anns,C,ν₀,listed,matched,tiedAccept,aligned,
        maximum,floor,nodeGuards,ready₀,transfer,coefEq,nonzero,equation⟩⟩
    · exact False.elim (nonzero zero)
  have zeroIf : maximalCoefficient (xs.map Prod.fst) a₀ = 0 →
      ∃ out : ReadState, CanonicalZeroWitness f B (extend baseline top z) r top s out a₀ := by
    intro zero
    rcases verdict with ⟨nonzero,_⟩ | ⟨_,out,witness,_⟩
    · exact False.elim (nonzero zero)
    · exact ⟨out,witness⟩
  obtain ⟨tied₀,accept₀⟩ := tiedAccept
  rw [frames] at listed matched tied₀ accept₀ stopIf zeroIf
  rw [atTop] at accept₀
  have signPaid : inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤
      extend baseline top z top := by
    rw [atTop]
    exact ctx.sign
  have available := exactFiniteFullValueGuards f B chosen baseline top
    (labels (groupTyped (syntaxOf s))) ready
  have exactGuard (a : List Answer) (member : a ∈ tapes (groupTyped (syntaxOf s))) :
      PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a) ↔
        Matches f (Function.update baseline top z)
          (pairs (labels (groupTyped (syntaxOf s)))) a := by
    obtain ⟨_,someTied,meaning⟩ := available.1 a member
    constructor
    · rintro ⟨ν,tied,accepts⟩
      exact (meaning ν tied z paid).mp accepts
    · intro matchedRaw
      obtain ⟨ν,tied⟩ := someTied
      exact ⟨ν,tied,(meaning ν tied z paid).mpr matchedRaw⟩
  have holds₀ : PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a₀) :=
    ⟨ν₀,(tiedBelow f (extend baseline top z) baseline top _ ν₀
      (fun i h => (below i h).symm)).mp tied₀,accept₀⟩
  refine ⟨exactGuard,⟨a₀,listed,holds₀⟩,?_⟩
  intro a member passing
  have rawMatch := (exactGuard a member).mp passing
  have matchHere : Matches f (extend baseline top z)
      (pairs (labels (groupTyped (syntaxOf s)))) a :=
    (matchedTransport f (extend baseline top z) (Function.update baseline top z) top
      rootReady.2.2 (labels (groupTyped (syntaxOf s))) (fun l used => (ready.1 l used).1) a).mpr
      rawMatch
  have same : a = a₀ := exactMatchedAnswerUnique f _ _ a a₀ matchHere matched
  rw [same]
  unfold RealBranch
  by_cases zero : maximalCoefficient (groupTyped (syntaxOf s)) a₀ = 0
  · obtain ⟨out,witness⟩ := zeroIf zero
    obtain ⟨literal,_,_,_,value,strict⟩ := exactCanonicalZeroReplay f B chosen
      (extend baseline top z) r top s out a₀ witness
    exact Or.inl ⟨zero,out,witness,literal,value,strict⟩
  · obtain ⟨xs',normal',_,branches'⟩ := exactFundedForwardTruth f B chosen
      (extend baseline top z) rootReady.1 r top initial s answers (sourceLive ctx.run)
      ctx.run.ranks ctx.run.long signPaid path (stopIf zero)
    have sameXs : xs' = xs := Option.some.inj (normal'.symm.trans normal)
    rw [sameXs] at branches'
    rcases branches' with ⟨idle,_⟩ | ⟨_,forward⟩
    · exact False.elim (idle activeAt)
    · obtain ⟨_,_,a',matched',_,tests⟩ := forward
      rw [frames] at matched' tests
      have again : a' = a₀ := exactMatchedAnswerUnique f _ _ a' a₀ matched' matched
      rw [again] at tests
      refine Or.inr ⟨zero,fun test positive => ?_⟩
      rw [← valueEq]
      exact tests test positive

end LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
