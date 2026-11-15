module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.ConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.CoreProof
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
open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof

theorem nonzero2 (D : Program 2) (G : Program 3) (raw query old param deps answers value out node tail : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hnode : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode node raw)))
    (htail : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  exact ConsProof.consCore D G raw node tail query old param deps answers value out hb (reconstructNonzero raw node tail hn hnode htail) hm hd ha hg ho

theorem nonzero1 (D : Program 2) (G : Program 3) (raw query old param deps answers value out node : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hnode : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode node raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (InternalListCodec.tailCode) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta tail hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hnj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hdj := renameInto hd j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have haj := renameInto ha j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hgj := renameInto hg j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hoj := renameInto ho j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hoj
  have hnodej := renameInto hnode j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnodej
  exact nonzero2 D G (raw.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (node.relabel j) tail hbj hnj hmj hdj haj hgj hoj hnodej hx

theorem nonzero (D : Program 2) (G : Program 3) (raw query old param deps answers value out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hn : Nonempty (Derivation body Delta ((eqn raw z).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (InternalListCodec.headCode) (Fin.cons raw (Fin.elim0)) _
  intro beta j Theta node hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn raw z).relabel j).not) at hnj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hdj := renameInto hd j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have haj := renameInto ha j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hgj := renameInto hg j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hgj
  have hoj := renameInto ho j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hoj
  exact nonzero1 D G (raw.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) node hbj hnj hmj hdj haj hgj hoj hx

theorem core (D : Program 2) (G : Program 3) (raw query old param deps answers value out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm0 := headTransport contains (numeral 1) raw z (Fin.cons query Fin.elim0) hz (withHyp hm A)
    have he := valueUnique contains (numeral 1) z ![z,query] hm0 (containsNil query)
    obtain ⟨e⟩ := he
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩
  · exact nonzero D G raw query old param deps answers value out (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not) (withHyp hd A.not)
      (withHyp ha A.not) (withHyp hg A.not) (withHyp ho A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.CoreProof
