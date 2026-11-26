module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.ConsProof
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

theorem distinctCons4 (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out rest nd na nv : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hn : Nonempty (Derivation body Delta ((eqn node query).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hnd : Nonempty (Derivation body Delta (graph2 D nd node param)))
    (hna : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph na nd old)))
    (hnv : Nonempty (Derivation body Delta (graph3 G nv node na param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  exact StepProof.atValues D G raw node tail query old param deps answers value out rest nd na nv hb hc hn hm hd ha hg ho hrest hnd hna hnv

theorem distinctCons3 (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out rest nd na : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hn : Nonempty (Derivation body Delta ((eqn node query).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hnd : Nonempty (Derivation body Delta (graph2 D nd node param)))
    (hna : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph na nd old)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (G) (Fin.cons node (Fin.cons na (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta nv hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node query).relabel j).not) at hnj
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
  have hrestj := renameInto hrest j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrestj
  have hndj := renameInto hnd j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hndj
  have hnaj := renameInto hna j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnaj
  exact distinctCons4 D G (raw.relabel j) (node.relabel j) (tail.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (nd.relabel j) (na.relabel j) nv hbj hcj hnj hmj hdj haj hgj hoj hrestj hndj hnaj hx

theorem distinctCons2 (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out rest nd : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hn : Nonempty (Derivation body Delta ((eqn node query).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hnd : Nonempty (Derivation body Delta (graph2 D nd node param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (ExchangeMapGraph.mapGraph) (Fin.cons nd (Fin.cons old (Fin.elim0))) _
  intro beta j Theta na hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node query).relabel j).not) at hnj
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
  have hrestj := renameInto hrest j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrestj
  have hndj := renameInto hnd j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hndj
  exact distinctCons3 D G (raw.relabel j) (node.relabel j) (tail.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (nd.relabel j) na hbj hcj hnj hmj hdj haj hgj hoj hrestj hndj hx

theorem distinctCons1 (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hn : Nonempty (Derivation body Delta ((eqn node query).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (D) (Fin.cons node (Fin.cons param (Fin.elim0))) _
  intro beta j Theta nd hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node query).relabel j).not) at hnj
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
  have hrestj := renameInto hrest j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrestj
  exact distinctCons2 D G (raw.relabel j) (node.relabel j) (tail.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) nd hbj hcj hnj hmj hdj haj hgj hoj hrestj hx

theorem distinctCons (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hn : Nonempty (Derivation body Delta ((eqn node query).not)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  apply programCases (ExchangeGraphStage.stage D G) (Fin.cons tail (Fin.cons old (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta rest hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node query).relabel j).not) at hnj
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
  exact distinctCons1 D G (raw.relabel j) (node.relabel j) (tail.relabel j) (query.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) rest hbj hcj hnj hmj hdj haj hgj hoj hx

theorem consCore (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw node tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw query)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps query param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) query answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out raw old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out query)) := by
  let A := eqn node query
  apply formulaCases A
  · have he : Nonempty (Derivation body (A :: Delta) (eqn node query)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨e⟩ := he
    have hd' := headTransport D deps query node (Fin.cons param Fin.elim0) ⟨symm e⟩ (withHyp hd A)
    have hg' := headTransport G (suc value) query node (Fin.cons answers (Fin.cons param Fin.elim0)) ⟨symm e⟩ (withHyp hg A)
    have hl := ExchangeStageLookup.HeadProof.headLookup body alpha (A :: Delta) D G raw node tail old param deps answers value out
      (withHyp hc A) hd' (withHyp ha A) hg' (withHyp ho A)
    unfold graph2 programGraph at hl ⊢
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 (A :: Delta)
      (OrdinaryArithmetic.graphFormula ExchangeMapGraph.lookup)
      (suc value) ![out,node] ![out,query] _ hl
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl out⟩
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      rw [InternalSourceInversionSupportProof.onEquality]
      exact he

  · exact distinctCons D G raw node tail query old param deps answers value out
      (withHyp hb A.not) (withHyp hc A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hm A.not) (withHyp hd A.not) (withHyp ha A.not) (withHyp hg A.not) (withHyp ho A.not)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.ConsProof
