module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.HeadProof
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
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)

theorem head3 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest pair table : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    (htable : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair rest)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out node)) := by
  have hc := SupportProof.actualCons D G frontier node tail old param deps answers value out rest pair table hf hd hm hg ho hrest hpair htable
  exact ExchangeMapGraph.InternalProof.internalFirstHit body alpha Delta out pair rest node value hc hpair

theorem head2 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest pair : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out node)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons pair (Fin.cons rest (Fin.elim0))) _
  intro beta j Theta table hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hgj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hoj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrestj
  have hpairj := renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hpairj
  exact head3 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (pair.relabel j) table hfj hdj hmj hgj hoj hrestj hpairj hx

theorem head1 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hrest : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out node)) := by
  apply programCases (InternalPairing.pairing) (Fin.cons node (Fin.cons value (Fin.elim0))) _
  intro beta j Theta pair hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hgj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hoj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrestj
  exact head2 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) pair hfj hdj hmj hgj hoj hrestj hx

theorem head (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) out node)) := by
  apply programCases (ExchangeGraphStage.stage D G) (Fin.cons tail (Fin.cons old (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta rest hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hmj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hgj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hoj
  exact head1 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) rest hfj hdj hmj hgj hoj hx

theorem headLookup : Targets.InternalHeadLookup := by
  intro body alpha Delta D G frontier node tail old param deps answers value out hf hd hm hg ho
  exact head D G frontier node tail old param deps answers value out hf hd hm hg ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.HeadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.HeadProof
