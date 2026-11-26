module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.StepProof
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
theorem atValues (D : Program 2) (G : Program 3) (raw node tail query old param deps answers value out rest nd na nv : OTerm alpha)
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
  have hneq : Nonempty (Derivation body Delta (equal node query).not) := by simpa only [equalEqn] using hn
  have hmt := PrimaryMembership.Proof.missRecover raw node tail query (numeral 1) hc hneq hm
  have hlt := belowRawApply D G raw tail query old param deps answers value rest hb
    (consTailDescent raw node tail hc) (andIntro hmt (andIntro hd (andIntro ha (andIntro hg hrest))))
  apply zeroSuccessorCases Delta nv _
  · let A := eqn nv z
    have hz : Nonempty (Derivation body (A :: Delta) (eqn nv z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hgz := outputTransport G nv z ![node,na,param] hz (withHyp hnv A)
    exact (ExchangeStageLookup.SkipProof.skippedLookup body alpha (A :: Delta) D G
      raw node tail old param nd na out rest query (suc value)
      (withHyp hc A) (withHyp hnd A) (withHyp hna A) hgz (withHyp ho A) (withHyp hrest A)).mpr (withHyp hlt A)
  · intro beta j Theta pred hj he
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
    have hnvj := renameInto hnv j Theta hj
    simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnvj
    have hltj := renameInto hlt j Theta hj
    unfold result at hltj
    simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hltj
    have hgs := outputTransport G (nv.relabel j) (suc pred)
      ![node.relabel j,na.relabel j,param.relabel j] he hnvj
    exact (ExchangeStageLookup.DistinctProof.distinctLookup body beta Theta D G
      (raw.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j)
      (nd.relabel j) (na.relabel j) pred (out.relabel j) (rest.relabel j) (query.relabel j) (suc (value.relabel j))
      hcj hndj hnaj hgs hnj hoj hrestj).mpr hltj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.StepProof
