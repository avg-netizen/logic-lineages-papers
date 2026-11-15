module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
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
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem atTable (R D : Program 2) (G : Program 3) (seed param rank old deps answers value nodes pair : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed answers param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons pair (Fin.cons z (Fin.elim0))) _
  intro beta j Theta table hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hfj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hpj
  exact FinalSupportProof.atWitnesses R D G (seed.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (nodes.relabel j) (pair.relabel j) table hdj hmj hgj hrj hoj hfj hpj hx

theorem atPair (R D : Program 2) (G : Program 3) (seed param rank old deps answers value nodes : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed answers param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalPairing.pairing) (Fin.cons seed (Fin.cons value (Fin.elim0))) _
  intro beta j Theta pair hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hfj
  exact atTable R D G (seed.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (nodes.relabel j) pair hrj hoj hdj hmj hgj hfj hx

theorem atNodes (R D : Program 2) (G : Program 3) (seed param rank old deps answers value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed answers param)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons seed (Fin.cons z (Fin.elim0))) _
  intro beta j Theta nodes hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  exact atPair R D G (seed.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) nodes hrj hoj hdj hmj hgj hx

theorem finalAnswers : Targets.InternalFinalAnswers := by
  intro body alpha Delta R D G seed param rank old deps answers value hr ho hd hm hg
  exact atNodes R D G seed param rank old deps answers value hr ho hd hm hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
