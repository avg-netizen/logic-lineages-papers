module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.CoreProof
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
open SideProof PresenceProof InputProof

def weakenSide {raw param : OTerm alpha} (s : Side body Delta raw param) (phi : Formula alpha) : Side body (phi :: Delta) raw param where
  index := s.index
  seed := s.seed
  depth := s.depth
  frontier := s.frontier
  table := s.table
  bounded := withHyp s.bounded phi
  subtraction := withHyp s.subtraction phi
  front := withHyp s.front phi
  member := withHyp s.member phi
  tableGraph := withHyp s.tableGraph phi

def weakenInput {raw param : OTerm alpha} (c : Input body Delta raw param) (phi : Formula alpha) : Input body (phi :: Delta) raw param where
  s1 := weakenSide c.s1 phi
  s2 := weakenSide c.s2 phi
  found := c.found
  below := withHyp c.below phi
  lookup := withHyp c.lookup phi

theorem nonConsAtOlds {raw param : OTerm alpha} (c : Input body Delta raw param) (tag old1 old2 : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) :=
  ArgumentEntriesNonConsCoherence.Proof.cacheTransport body alpha Delta raw tag param c.s1.frontier c.s2.frontier
    old1 old2 c.s1.table c.s2.table c.found ht hn (sideStage c.s1 old1 ho1) (sideStage c.s2 old2 ho2)
    c.s1.member c.s2.member c.lookup

theorem nonConsAtOld1 {raw param : OTerm alpha} (c : Input body Delta raw param) (tag old1 : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons c.s2.index (Fin.cons c.s2.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old2 hj ho2
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at ho2
  have htj := renameInto ht j Theta hj
  rw [graph1Rename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hoj := renameInto ho1 j Theta hj
  rw [graph3Rename] at hoj
  exact nonConsAtOlds (c.rename j Theta hj) (tag.relabel j) (old1.relabel j) old2 htj hnj hoj ho2

theorem nonCons {raw param : OTerm alpha} (c : Input body Delta raw param) (tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not)) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons c.s1.index (Fin.cons c.s1.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old1 hj ho1
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at ho1
  have htj := renameInto ht j Theta hj
  rw [graph1Rename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  exact nonConsAtOld1 (c.rename j Theta hj) (tag.relabel j) old1 htj hnj ho1

theorem atTag {raw param : OTerm alpha} (c : Input body Delta raw param) (tag : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply formulaCases (eqn tag (numeral 7))
  · let cp := weakenInput c (eqn tag (numeral 7))
    have h7 := outputTransport InternalUnpair.left tag (numeral 7) (Fin.cons raw Fin.elim0)
      ⟨Derivation.hypothesis (body := body) (Gamma := eqn tag (numeral 7) :: Delta) List.mem_cons_self⟩ (withHyp ht _)
    apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw _ h7
    intro beta j Theta tau head tail hj hc
    rw [graph2Rename]
    exact ConsProof.close { toInput := cp.rename j Theta hj, tau := tau, head := head, tail := tail, constructor := hc }
  · exact nonCons (weakenInput c (eqn tag (numeral 7)).not) tag (withHyp ht _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem close {raw param : OTerm alpha} (c : Input body Delta raw param) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply programCases InternalUnpair.left (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at ht
  exact atTag (c.rename j Theta hj) tag ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.CoreProof
