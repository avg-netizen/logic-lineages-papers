module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.DistinctProof
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

theorem forward2 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result pair table : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    (htable : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair rest)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)) := by
  have hc := SupportProof.actualCons D G frontier node tail old param deps answers value out rest pair table hf hd hm hg ho hr hpair htable
  exact (ExchangeMapGraph.InternalProof.internalMissTail body alpha Delta out pair rest node value key result hc hpair hn).mp hl

theorem forward1 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result pair : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)) := by
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
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node key).relabel j).not) at hnj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hlj
  have hpairj := renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hpairj
  exact forward2 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (key.relabel j) (result.relabel j) (pair.relabel j) table hfj hdj hmj hgj hoj hrj hnj hlj hpairj hx

theorem forward (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)) := by
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
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node key).relabel j).not) at hnj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hlj
  exact forward1 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (key.relabel j) (result.relabel j) pair hfj hdj hmj hgj hoj hrj hnj hlj hx

theorem backward2 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result pair table : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    (htable : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair rest)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)) := by
  have hc := SupportProof.actualCons D G frontier node tail old param deps answers value out rest pair table hf hd hm hg ho hr hpair htable
  exact (ExchangeMapGraph.InternalProof.internalMissTail body alpha Delta out pair rest node value key result hc hpair hn).mpr hl

theorem backward1 (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result pair : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)) := by
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
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node key).relabel j).not) at hnj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hlj
  have hpairj := renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hpairj
  exact backward2 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (key.relabel j) (result.relabel j) (pair.relabel j) table hfj hdj hmj hgj hoj hrj hnj hlj hpairj hx

theorem backward (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest key result : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hn : Nonempty (Derivation body Delta ((eqn node key).not)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result rest key)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup result out key)) := by
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
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hrj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn node key).relabel j).not) at hnj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hlj
  exact backward1 D G (frontier.relabel j) (node.relabel j) (tail.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) (value.relabel j) (out.relabel j) (rest.relabel j) (key.relabel j) (result.relabel j) pair hfj hdj hmj hgj hoj hrj hnj hlj hx

theorem distinctLookup : Targets.InternalDistinctLookup := by
  intro body alpha Delta D G frontier node tail old param deps answers value out rest key result hf hd hm hg hn ho hr
  constructor
  · exact forward D G frontier node tail old param deps answers value out rest key result hf hd hm hg ho hr hn
  · exact backward D G frontier node tail old param deps answers value out rest key result hf hd hm hg ho hr hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.DistinctProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.DistinctProof
