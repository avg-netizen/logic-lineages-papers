module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.SideProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.RankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.FrameProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 SideProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
structure Frame (n : Nat) (body : Positive (Fin 1))
    {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha) where
  s1 : Side n body Delta raw param
  s2 : Side n body Delta raw param
  old1 : OTerm alpha
  old2 : OTerm alpha
  pred1 : OTerm alpha
  pred2 : OTerm alpha
  next1 : OTerm alpha
  next2 : OTerm alpha
  index1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1)))
  oldGraph1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param))
  nextGraph1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next1 (suc s1.depth) s1.seed param))
  index2 : Nonempty (Derivation body Delta (eqn s2.index (suc pred2)))
  oldGraph2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param))
  nextGraph2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next2 (suc s2.depth) s2.seed param))

def Frame.rename {raw param : OTerm alpha} (f : Frame n body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) : Frame n body Theta (raw.relabel j) (param.relabel j) where
  s1 := f.s1.rename j Theta hj
  s2 := f.s2.rename j Theta hj
  old1 := f.old1.relabel j
  old2 := f.old2.relabel j
  pred1 := f.pred1.relabel j
  pred2 := f.pred2.relabel j
  next1 := f.next1.relabel j
  next2 := f.next2.relabel j
  index1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.index1 j Theta hj
    simpa only [Side.rename,eqnRelabel,sucRelabel] using h
  oldGraph1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.oldGraph1 j Theta hj
    simpa only [Side.rename,graph3Rename,sucRelabel] using h
  nextGraph1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.nextGraph1 j Theta hj
    simpa only [Side.rename,graph3Rename,sucRelabel] using h
  index2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.index2 j Theta hj
    simpa only [Side.rename,eqnRelabel,sucRelabel] using h
  oldGraph2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.oldGraph2 j Theta hj
    simpa only [Side.rename,graph3Rename,sucRelabel] using h
  nextGraph2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.nextGraph2 j Theta hj
    simpa only [Side.rename,graph3Rename,sucRelabel] using h

theorem ihApply {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget rank found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank raw param)))
    (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess rank budget)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply BindingProof.belowRawApply n budget rank raw param
    s1.index s1.seed s1.seedRank s1.depth s1.frontier s1.table
    s2.index s2.seed s2.seedRank s2.depth s2.frontier s2.table found ih hlt
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (hr) s1.rankGraph) s1.bounded) s1.subtraction) s1.front) s1.member) s1.tableGraph) s2.rankGraph) s2.bounded) s2.subtraction) s2.front) s2.member) s2.tableGraph) hl

theorem childTransportAt {raw param : OTerm alpha} (f : Frame n body Delta raw param)
    (budget deps child childRank found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) deps child)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank childRank child param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.old1 child))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.old2 child)) := by
  let c1 := previousSide f.s1 f.pred1 f.old1 f.next1 child f.index1 f.oldGraph1 f.nextGraph1
    (childMember f.s1 deps child f.next1 hd hm f.nextGraph1)
  let c2 := previousSide f.s2 f.pred2 f.old2 f.next2 child f.index2 f.oldGraph2 f.nextGraph2
    (childMember f.s2 deps child f.next2 hd hm f.nextGraph2)
  exact ihApply c1 c2 budget childRank found ih hc
    (RankProof.rankDecrease body alpha Delta raw param deps child budget childRank hd hm hr hc) hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.FrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.FrameProof
