module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.PresenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SideProof PresenceProof

structure Frame (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha) where
  s1 : Side body Delta raw param
  s2 : Side body Delta raw param
  tau : OTerm alpha
  head : OTerm alpha
  tail : OTerm alpha
  pred1 : OTerm alpha
  pred2 : OTerm alpha
  old1 : OTerm alpha
  old2 : OTerm alpha
  next1 : OTerm alpha
  next2 : OTerm alpha
  deps : OTerm alpha
  found : OTerm alpha
  constructor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail))
  index1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1)))
  index2 : Nonempty (Derivation body Delta (eqn s2.index (suc pred2)))
  oldGraph1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 s1.index s1.seed param))
  oldGraph2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 s2.index s2.seed param))
  nextGraph1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next1 (suc s1.depth) s1.seed param))
  nextGraph2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next2 (suc s2.depth) s2.seed param))
  dependency : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param))
  headMember : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps head))
  tailMember : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps tail))
  below : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw raw))
  lookup : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))

def Frame.rename {raw param : OTerm alpha} (f : Frame body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) : Frame body Theta (raw.relabel j) (param.relabel j) where
  s1 := f.s1.rename j Theta hj
  s2 := f.s2.rename j Theta hj
  tau := f.tau.relabel j
  head := f.head.relabel j
  tail := f.tail.relabel j
  pred1 := f.pred1.relabel j
  pred2 := f.pred2.relabel j
  old1 := f.old1.relabel j
  old2 := f.old2.relabel j
  next1 := f.next1.relabel j
  next2 := f.next2.relabel j
  deps := f.deps.relabel j
  found := f.found.relabel j
  constructor := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.constructor j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  index1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.index1 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  index2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.index2 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  oldGraph1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.oldGraph1 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  oldGraph2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.oldGraph2 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  nextGraph1 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.nextGraph1 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  nextGraph2 := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.nextGraph2 j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  dependency := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.dependency j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  headMember := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.headMember j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  tailMember := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.tailMember j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  below := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.below j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h
  lookup := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.lookup j Theta hj
    simpa only [graph2Rename,graph3Rename,sucRelabel,eqnRelabel,GuardedSourceSyntaxProof.numeralRename,InductionSyntaxProof.belowRawRename] using h

def Frame.head1 {raw param : OTerm alpha} (f : Frame body Delta raw param) : Side body Delta f.head param :=
  previousSide f.s1 f.pred1 f.old1 f.next1 f.head f.index1 f.oldGraph1 f.nextGraph1
    (childMember f.s1 f.deps f.head f.next1 f.dependency f.headMember f.nextGraph1)

def Frame.tail1 {raw param : OTerm alpha} (f : Frame body Delta raw param) : Side body Delta f.tail param :=
  previousSide f.s1 f.pred1 f.old1 f.next1 f.tail f.index1 f.oldGraph1 f.nextGraph1
    (childMember f.s1 f.deps f.tail f.next1 f.dependency f.tailMember f.nextGraph1)

def Frame.head2 {raw param : OTerm alpha} (f : Frame body Delta raw param) : Side body Delta f.head param :=
  previousSide f.s2 f.pred2 f.old2 f.next2 f.head f.index2 f.oldGraph2 f.nextGraph2
    (childMember f.s2 f.deps f.head f.next2 f.dependency f.headMember f.nextGraph2)

def Frame.tail2 {raw param : OTerm alpha} (f : Frame body Delta raw param) : Side body Delta f.tail param :=
  previousSide f.s2 f.pred2 f.old2 f.next2 f.tail f.index2 f.oldGraph2 f.nextGraph2
    (childMember f.s2 f.deps f.tail f.next2 f.dependency f.tailMember f.nextGraph2)

theorem atValues {raw param : OTerm alpha} (f : Frame body Delta raw param) (left1 left2 value : OTerm alpha)
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) f.old1 f.head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) f.old2 f.head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) f.old1 f.tail))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup f.found f.s2.table raw)) := by
  have hlt := SupportProof.consTailStrict raw f.tau f.head f.tail f.constructor
  have ht2 := smallerApply f.tail1 f.tail2 (suc value) f.below hlt ht1
  exact ArgumentEntriesTailCoherence.Proof.consTransport body alpha Delta raw f.tau f.head f.tail param
    f.s1.frontier f.s2.frontier f.old1 f.old2 f.s1.table f.s2.table left1 left2 value f.found f.constructor
    (sideStage f.s1 f.old1 f.oldGraph1) (sideStage f.s2 f.old2 f.oldGraph2)
    f.s1.member f.s2.member hh1 hh2 ht1 ht2 f.lookup

theorem atHeads {raw param : OTerm alpha} (f : Frame body Delta raw param) (left1 left2 : OTerm alpha)
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) f.old1 f.head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) f.old2 f.head))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup f.found f.s2.table raw)) := by
  apply presentCases f.tail1 _
  intro beta j Theta value hj ht
  rw [graph2Rename]
  have h1 := InternalGraphCompositionFunctionalityProof.renameInto hh1 j Theta hj
  have h2 := InternalGraphCompositionFunctionalityProof.renameInto hh2 j Theta hj
  simp only [graph2Rename,sucRelabel] at h1 h2
  exact atValues (f.rename j Theta hj) (left1.relabel j) (left2.relabel j) value h1 h2 ht

theorem atHead1 {raw param : OTerm alpha} (f : Frame body Delta raw param) (left1 : OTerm alpha)
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) f.old1 f.head))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup f.found f.s2.table raw)) := by
  apply presentCases f.head2 _
  intro beta j Theta left2 hj hh2
  rw [graph2Rename]
  have h1 := InternalGraphCompositionFunctionalityProof.renameInto hh1 j Theta hj
  simp only [graph2Rename,sucRelabel] at h1
  exact atHeads (f.rename j Theta hj) (left1.relabel j) left2 h1 hh2

theorem close {raw param : OTerm alpha} (f : Frame body Delta raw param) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup f.found f.s2.table raw)) := by
  apply presentCases f.head1 _
  intro beta j Theta left1 hj hh1
  rw [graph2Rename]
  exact atHead1 (f.rename j Theta hj) left1 hh1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsFrameProof
