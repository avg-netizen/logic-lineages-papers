module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SideProof
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

structure Side (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha) where
  index : OTerm alpha
  seed : OTerm alpha
  depth : OTerm alpha
  frontier : OTerm alpha
  table : OTerm alpha
  bounded : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed))
  subtraction : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed))
  front : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param))
  member : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw))
  tableGraph : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param))

def Side.rename {raw param : OTerm alpha} (s : Side body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) : Side body Theta (raw.relabel j) (param.relabel j) where
  index := s.index.relabel j
  seed := s.seed.relabel j
  depth := s.depth.relabel j
  frontier := s.frontier.relabel j
  table := s.table.relabel j
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

theorem graphIndexTransport (out index next seed param : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn index next)))
    (hg : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph out index seed param))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph out next seed param)) := by
  unfold graph3 programGraph at hg ⊢
  apply graphInputTransport body alpha 3 Delta (OrdinaryArithmetic.graphFormula ArgumentEntriesRecursor.graph) out
    (Fin.cons index (Fin.cons seed (Fin.cons param Fin.elim0)))
    (Fin.cons next (Fin.cons seed (Fin.cons param Fin.elim0))) _ hg
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun q => Fin.elim0 q) l) k) i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl seed⟩
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl param⟩

def previousSide {raw param : OTerm alpha} (s : Side body Delta raw param)
    (pred old next child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (eqn s.index (suc pred))))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old s.index s.seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next (suc s.depth) s.seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) next child))) : Side body Delta child param where
  index := pred
  seed := s.seed
  depth := suc s.depth
  frontier := next
  table := old
  bounded := by
    have hb := PrimaryUncoveredCount.OrderProof.transport s.index s.seed (suc pred) s.seed hi ⟨refl s.seed⟩ s.bounded
    exact SupportProof.predecessorBound pred s.seed hb
  subtraction := by
    have hb := PrimaryUncoveredCount.OrderProof.transport s.index s.seed (suc pred) s.seed hi ⟨refl s.seed⟩ s.bounded
    have hs := InternalEqualityTestSubtractionSupportProof.subTransport s.depth s.index s.seed (suc pred) s.seed
      hi ⟨refl s.seed⟩ s.subtraction
    exact SubtractionAlignment.Proof.predecessorAlignment body alpha Delta pred s.seed s.depth hb hs
  front := hf
  member := hm
  tableGraph := graphIndexTransport old s.index (suc pred) s.seed param hi ho

theorem childMember {raw param : OTerm alpha} (s : Side body Delta raw param)
    (deps child next : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hc : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hn : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next (suc s.depth) s.seed param))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) next child)) :=
  ExchangeFrontierCoverage.Proof.successorCoverage body alpha Delta ArgumentEntriesRecursor.dependency
    s.depth s.seed param s.frontier raw deps child next s.front s.member hd hc hn

theorem lookupNonzero {raw param : OTerm alpha} (s : Side body Delta raw param) (found : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s.table raw))) :
    Nonempty (Derivation body Delta (eqn found z).not) :=
  ArgumentEntriesTableDomain.Proof.successorDomain body alpha Delta s.index s.seed param s.depth s.frontier s.table raw found
    s.subtraction s.front s.tableGraph s.member hl

theorem sideStage {raw param : OTerm alpha} (s : Side body Delta raw param) (old : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old s.index s.seed param))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) s.table s.frontier old param)) :=
  SupportProof.stage s.index s.seed param s.depth s.frontier s.table old s.subtraction s.front s.tableGraph ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SideProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SideProof
