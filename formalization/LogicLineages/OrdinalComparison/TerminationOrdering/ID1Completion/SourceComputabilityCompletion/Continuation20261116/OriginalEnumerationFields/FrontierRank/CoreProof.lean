module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open InductionDefinitions InductionSyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroCore (seed param frontier child seedRank childRank : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    : Nonempty (Derivation body Delta (result z seedRank childRank)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta listCode hj hlist
  simp only [consTermRename,emptyRename,zRelabel] at hlist
  simp only [resultRename,zRelabel]
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hmj
  have hsj := renameInto hs j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hsj
  have hcj := renameInto hc j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hcj
  exact FrontierRankSupportProof.zeroAt (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) (seedRank.relabel j) (childRank.relabel j) listCode hfj hmj hsj hcj hlist

theorem successorRank (depth seed param frontier child seedRank childRank previous node nodeRank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) previous depth seed param)))
    (hmem : Nonempty (Derivation body Delta (graph2 contains (numeral 1) previous node)))
    (hedge : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge dependency) (numeral 1) node child param)))
    (hnr : Nonempty (Derivation body Delta (graph2 rank nodeRank node param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  have hb := rowApply depth seed param previous node seedRank nodeRank hi hp hmem hs hnr
  exact PrimaryFiniteDescent.ArithmeticProof.budgetStep depth nodeRank childRank seedRank
    (FrontierRankSupportProof.edgeDescent node child param nodeRank childRank hedge hnr hc) hb

theorem successorNode (depth seed param frontier child seedRank childRank previous node : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) previous depth seed param)))
    (hmem : Nonempty (Derivation body Delta (graph2 contains (numeral 1) previous node)))
    (hedge : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge dependency) (numeral 1) node child param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  apply programCases rank (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta nodeRank hj hnr
  simp only [consTermRename,emptyRename] at hnr
  simp only [resultRename,sucRelabel]
  have hij := renameInto hi j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hij
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hmj
  have hsj := renameInto hs j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hsj
  have hcj := renameInto hc j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hcj
  have hpj := renameInto hp j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hpj
  have hmemj := renameInto hmem j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hmemj
  have hedgej := renameInto hedge j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hedgej
  exact successorRank (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) (seedRank.relabel j) (childRank.relabel j) (previous.relabel j) (node.relabel j) nodeRank hij hfj hmj hsj hcj hpj hmemj hedgej hnr

theorem successorAt (depth seed param frontier child seedRank childRank previous : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) previous depth seed param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  have hw := ExchangeFrontierWitness.Proof.successorWitness body alpha Delta dependency depth seed param previous frontier child hp hf hm
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness (ExchangeFrontierWitness.dependencyEdge dependency) previous child param _ hw
  intro beta j Theta node hj hmem hedge
  simp only [resultRename,sucRelabel]
  have hij := renameInto hi j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hij
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hmj
  have hsj := renameInto hs j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hsj
  have hcj := renameInto hc j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hcj
  have hpj := renameInto hp j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hpj
  exact successorNode (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) (seedRank.relabel j) (childRank.relabel j) (previous.relabel j) node hij hfj hmj hsj hcj hpj hmem hedge

theorem successorCore (depth seed param frontier child seedRank childRank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  apply programCases (ExchangeFrontier.bindList dependency) (Fin.cons depth (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta previous hj hp
  simp only [consTermRename,emptyRename] at hp
  simp only [resultRename,sucRelabel]
  have hij := renameInto hi j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hij
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hmj
  have hsj := renameInto hs j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hsj
  have hcj := renameInto hc j Theta hj
  simp only [graph3Rename,graph2Rename,zRelabel,sucRelabel,GuardedSourceSyntaxProof.numeralRename,atCountRename] at hcj
  exact successorAt (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) (seedRank.relabel j) (childRank.relabel j) previous hij hfj hmj hsj hcj hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.CoreProof
