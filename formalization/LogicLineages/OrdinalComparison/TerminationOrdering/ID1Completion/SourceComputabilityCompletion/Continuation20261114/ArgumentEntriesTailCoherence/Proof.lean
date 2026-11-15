module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem atAnswers (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found deps answers1 answers2 : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)))
    (ht2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers1 deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers2 deps old2))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ArgumentEntriesLayer.step (Fin.cons raw (Fin.cons tailValue Fin.elim0)) _
  intro beta j Theta inner hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hh1j := renameInto hh1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh1j
  have hh2j := renameInto hh2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh2j
  have ht1j := renameInto ht1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht1j
  have ht2j := renameInto ht2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht2j
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have ha1j := renameInto ha1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ha1j
  have ha2j := renameInto ha2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ha2j
  exact SupportProof.atValues (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (left1.relabel j) (left2.relabel j) (tailValue.relabel j) (found.relabel j) (deps.relabel j) (answers1.relabel j) (answers2.relabel j) inner hcj hs1j hs2j hm1j hm2j hh1j hh2j ht1j ht2j hlj hdj ha1j ha2j hx

theorem atFirstAnswers (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found deps answers1 : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)))
    (ht2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers1 deps old1))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old2 Fin.elim0)) _
  intro beta j Theta answers2 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hh1j := renameInto hh1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh1j
  have hh2j := renameInto hh2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh2j
  have ht1j := renameInto ht1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht1j
  have ht2j := renameInto ht2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht2j
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have ha1j := renameInto ha1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ha1j
  exact atAnswers (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (left1.relabel j) (left2.relabel j) (tailValue.relabel j) (found.relabel j) (deps.relabel j) (answers1.relabel j) answers2 hcj hs1j hs2j hm1j hm2j hh1j hh2j ht1j ht2j hlj hdj ha1j hx

theorem atDeps (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found deps : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)))
    (ht2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old1 Fin.elim0)) _
  intro beta j Theta answers1 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hh1j := renameInto hh1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh1j
  have hh2j := renameInto hh2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh2j
  have ht1j := renameInto ht1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht1j
  have ht2j := renameInto ht2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht2j
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact atFirstAnswers (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (left1.relabel j) (left2.relabel j) (tailValue.relabel j) (found.relabel j) (deps.relabel j) answers1 hcj hs1j hs2j hm1j hm2j hh1j hh2j ht1j ht2j hlj hdj hx

theorem transport (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)))
    (ht2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
 :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ArgumentEntriesRecursor.dependency (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hh1j := renameInto hh1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh1j
  have hh2j := renameInto hh2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hh2j
  have ht1j := renameInto ht1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht1j
  have ht2j := renameInto ht2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at ht2j
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact atDeps (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (left1.relabel j) (left2.relabel j) (tailValue.relabel j) (found.relabel j) deps hcj hs1j hs2j hm1j hm2j hh1j hh2j ht1j ht2j hlj hx

theorem consTransport : Targets.InternalConsTransport := by
  intro body alpha Delta raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found hc hs1 hs2 hm1 hm2 hh1 hh2 ht1 ht2 hl
  exact transport raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found hc hs1 hs2 hm1 hm2 hh1 hh2 ht1 ht2 hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Proof
