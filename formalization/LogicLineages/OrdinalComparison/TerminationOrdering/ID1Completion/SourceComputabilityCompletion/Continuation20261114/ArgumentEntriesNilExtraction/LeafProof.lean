module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafProof
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

theorem atTable (R D : Program 2) (G : Program 3) (seed param value rank old nodes pair : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons pair (Fin.cons z (Fin.elim0))) _
  intro beta j Theta table hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hfj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hpj
  exact LeafSupportProof.atWitnesses R D G (seed.relabel j) (param.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (nodes.relabel j) (pair.relabel j) table hdj hgj hrj hoj hfj hpj hx

theorem atPair (R D : Program 2) (G : Program 3) (seed param value rank old nodes : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalPairing.pairing) (Fin.cons seed (Fin.cons value (Fin.elim0))) _
  intro beta j Theta pair hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hfj
  exact atTable R D G (seed.relabel j) (param.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (nodes.relabel j) pair hdj hgj hrj hoj hfj hx

theorem atNodes (R D : Program 2) (G : Program 3) (seed param value rank old : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons seed (Fin.cons z (Fin.elim0))) _
  intro beta j Theta nodes hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  exact atPair R D G (seed.relabel j) (param.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) nodes hdj hgj hrj hoj hx

theorem atOld (R D : Program 2) (G : Program 3) (seed param value rank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (ExchangeGraphRecursion.graph R D G) (Fin.cons rank (Fin.cons seed (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta old hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  exact atNodes R D G (seed.relabel j) (param.relabel j) (value.relabel j) (rank.relabel j) old hdj hgj hrj hx

theorem atRank (R D : Program 2) (G : Program 3) (seed param value : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    : Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  apply programCases (R) (Fin.cons seed (Fin.cons param (Fin.elim0))) _
  intro beta j Theta rank hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph2Rename]
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hgj := renameInto hg j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hgj
  exact atOld R D G (seed.relabel j) (param.relabel j) (value.relabel j) rank hdj hgj hx

theorem leaf : Targets.InternalLeaf := by
  intro body alpha Delta R D G seed param value hd hg
  exact atRank R D G seed param value hd hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafProof
