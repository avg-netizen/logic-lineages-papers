module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Proof
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

open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalAcceptanceBranchProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransport (constant)
theorem atValues (six : Bool) (raw tag param frontier1 frontier2 old1 old2 table1 table2 found deps answers1 answers2 : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (StepProof.caseFormula six tag)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers1 deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers2 deps old2))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  have hg1 := StepProof.canonicalLayer six raw tag answers1 param ht hn hc
  have hg2 := StepProof.canonicalLayer six raw tag answers2 param ht hn hc
  have h1 := ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier1 raw old1 param deps answers1 (numeral (if six then 1 else 0)) table1 hm1 hd ha1 hg1 hs1
  have h2 := ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier2 raw old2 param deps answers2 (numeral (if six then 1 else 0)) table2 hm2 hd ha2 hg2 hs2
  have he := valueUnique ExchangeMapGraph.lookup (suc (numeral (if six then 1 else 0))) found
    (Fin.cons table1 (Fin.cons raw Fin.elim0)) h1 hl
  exact outputTransport ExchangeMapGraph.lookup (suc (numeral (if six then 1 else 0))) found
    (Fin.cons table2 (Fin.cons raw Fin.elim0)) he h2

theorem atFirstAnswers (six : Bool) (raw tag param frontier1 frontier2 old1 old2 table1 table2 found deps answers1 : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (StepProof.caseFormula six tag)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers1 deps old1))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old2 Fin.elim0)) _
  intro beta j Theta answers2 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hcj := renameInto hc j Theta hj
  rw [StepProof.caseRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
  have ha1j := renameInto ha1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at ha1j
  exact atValues six (raw.relabel j) (tag.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (found.relabel j) (deps.relabel j) (answers1.relabel j) answers2 htj hnj hcj hs1j hs2j hm1j hm2j hlj hdj ha1j hx

theorem atDeps (six : Bool) (raw tag param frontier1 frontier2 old1 old2 table1 table2 found deps : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (StepProof.caseFormula six tag)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old1 Fin.elim0)) _
  intro beta j Theta answers1 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hcj := renameInto hc j Theta hj
  rw [StepProof.caseRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact atFirstAnswers six (raw.relabel j) (tag.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (found.relabel j) (deps.relabel j) answers1 htj hnj hcj hs1j hs2j hm1j hm2j hlj hdj hx

theorem transportCase (six : Bool) (raw tag param frontier1 frontier2 old1 old2 table1 table2 found : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
    (hn : Nonempty (Derivation body Delta (eqn tag (numeral 7)).not))
    (hc : Nonempty (Derivation body Delta (StepProof.caseFormula six tag)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
 :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  apply programCases ArgumentEntriesRecursor.dependency (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn tag (numeral 7)).relabel j).not) at hnj
  simp only [eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hcj := renameInto hc j Theta hj
  rw [StepProof.caseRename] at hcj
  have hs1j := renameInto hs1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs1j
  have hs2j := renameInto hs2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hs2j
  have hm1j := renameInto hm1 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm1j
  have hm2j := renameInto hm2 j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hm2j
  have hlj := renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact atDeps six (raw.relabel j) (tag.relabel j) (param.relabel j) (frontier1.relabel j) (frontier2.relabel j) (old1.relabel j) (old2.relabel j) (table1.relabel j) (table2.relabel j) (found.relabel j) deps htj hnj hcj hs1j hs2j hm1j hm2j hlj hx

theorem cacheTransport : Targets.InternalCacheTransport := by
  intro body alpha Delta raw tag param frontier1 frontier2 old1 old2 table1 table2 found ht hn hs1 hs2 hm1 hm2 hl
  apply formulaCases (eqn tag (numeral 6))
  · exact transportCase true raw tag param frontier1 frontier2 old1 old2 table1 table2 found
      (withHyp ht _) (withHyp hn _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hs1 _) (withHyp hs2 _) (withHyp hm1 _) (withHyp hm2 _) (withHyp hl _)
  · exact transportCase false raw tag param frontier1 frontier2 old1 old2 table1 table2 found
      (withHyp ht _) (withHyp hn _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hs1 _) (withHyp hs2 _) (withHyp hm1 _) (withHyp hm2 _) (withHyp hl _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.Proof
