module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.DomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.CapacityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.SideProof
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
open InternalGraphCompositionEqualityProof

structure Side (n : Nat) (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha) where
  index : OTerm alpha
  seed : OTerm alpha
  seedRank : OTerm alpha
  depth : OTerm alpha
  frontier : OTerm alpha
  table : OTerm alpha
  rankGraph : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param))
  bounded : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seedRank))
  subtraction : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seedRank))
  front : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param))
  member : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw))
  tableGraph : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) table (suc index) seed param))

variable {n : Nat}

def Side.rename {raw param : OTerm alpha} (s : Side n body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) : Side n body Theta (raw.relabel j) (param.relabel j) where
  index := s.index.relabel j
  seed := s.seed.relabel j
  seedRank := s.seedRank.relabel j
  depth := s.depth.relabel j
  frontier := s.frontier.relabel j
  table := s.table.relabel j
  rankGraph := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.rankGraph j Theta hj
    simpa only [graph2Rename] using h
  bounded := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.bounded j Theta hj
    simpa only [PrimaryUncoveredCount.OrderProof.boundedRename] using h
  subtraction := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.subtraction j Theta hj
    simpa only [graph2Rename] using h
  front := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.front j Theta hj
    simpa only [graph3Rename] using h
  member := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.member j Theta hj
    simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using h
  tableGraph := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.tableGraph j Theta hj
    simpa only [graph3Rename,sucRelabel] using h

theorem graphIndexTransport (n : Nat) (out index next seed param : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn index next)))
    (hg : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) out index seed param))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) out next seed param)) := by
  unfold graph3 programGraph at hg ⊢
  apply graphInputTransport body alpha 3 Delta (OrdinaryArithmetic.graphFormula (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n))) out
    (Fin.cons index (Fin.cons seed (Fin.cons param Fin.elim0)))
    (Fin.cons next (Fin.cons seed (Fin.cons param Fin.elim0))) _ hg
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun q => Fin.elim0 q) l) k) i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl seed⟩
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl param⟩

def previousSide {raw param : OTerm alpha} (s : Side n body Delta raw param)
    (pred old next child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (eqn s.index (suc pred))))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) old s.index s.seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) next (suc s.depth) s.seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) next child))) : Side n body Delta child param where
  index := pred
  seed := s.seed
  seedRank := s.seedRank
  rankGraph := s.rankGraph
  depth := suc s.depth
  frontier := next
  table := old
  bounded := by
    have hb := PrimaryUncoveredCount.OrderProof.transport s.index s.seedRank (suc pred) s.seedRank hi ⟨refl s.seedRank⟩ s.bounded
    exact CrossRootCacheCoherence.SupportProof.predecessorBound pred s.seedRank hb
  subtraction := by
    have hb := PrimaryUncoveredCount.OrderProof.transport s.index s.seedRank (suc pred) s.seedRank hi ⟨refl s.seedRank⟩ s.bounded
    have hs := InternalEqualityTestSubtractionSupportProof.subTransport s.depth s.index s.seedRank (suc pred) s.seedRank
      hi ⟨refl s.seedRank⟩ s.subtraction
    exact SubtractionAlignment.Proof.predecessorAlignment body alpha Delta pred s.seedRank s.depth hb hs
  front := hf
  member := hm
  tableGraph := graphIndexTransport n old s.index (suc pred) s.seed param hi ho

theorem childMember {raw param : OTerm alpha} (s : Side n body Delta raw param)
    (deps child next : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.D deps raw param)))
    (hc : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hn : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) next (suc s.depth) s.seed param))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) next child)) :=
  ExchangeFrontierCoverage.Proof.successorCoverage body alpha Delta OriginalEnumerationRecursionInterface.D
    s.depth s.seed param s.frontier raw deps child next s.front s.member hd hc hn

theorem lookupNonzero {raw param : OTerm alpha} (s : Side n body Delta raw param) (found : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s.table raw))) :
    Nonempty (Derivation body Delta (eqn found z).not) :=
  OriginalEnumerationCacheCoherence.DomainProof.successorDomain n body alpha Delta s.index s.seed param s.seedRank s.depth s.frontier s.table raw found
    s.rankGraph s.subtraction s.front s.tableGraph s.member hl

theorem sideStage {raw param : OTerm alpha} (s : Side n body Delta raw param) (old : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) old s.index s.seed param))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) s.table s.frontier old param)) :=
  (ExchangeGraphRecursion.InternalProof.internalSuccessor body alpha Delta
    OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)
    s.index s.seed param old s.seedRank s.depth s.frontier s.table ho s.rankGraph s.subtraction s.front).mp s.tableGraph

theorem capacity {raw param : OTerm alpha} (s : Side n body Delta raw param) (nodeRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R nodeRank raw param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded nodeRank s.index)) :=
  OriginalEnumerationCacheCoherence.CapacityProof.capacityAt n s.index s.seed param s.depth s.frontier raw s.seedRank nodeRank
    s.rankGraph s.bounded s.subtraction s.front s.member hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.SideProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.SideProof
