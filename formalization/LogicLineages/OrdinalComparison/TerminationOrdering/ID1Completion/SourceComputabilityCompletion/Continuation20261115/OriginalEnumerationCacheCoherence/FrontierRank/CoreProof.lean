module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.DecreaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.CoreProof
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
open InternalAdditionLawsProof (leftZero)
open Continuation20261114
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)


open SupportProof

theorem successorNode (n : Nat) (depth seed param previous node child seedRank childRank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount n depth)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) previous depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) previous node)))
    (he : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge OriginalEnumerationRecursionInterface.D) (numeral 1) node child param)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R childRank child param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  apply programCases OriginalEnumerationRecursionInterface.R (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta nodeRank hj hn
  simp only [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hn
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  rw [atCountRename] at hij
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hej
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hb := rowApply n (depth.relabel j) (seed.relabel j) (param.relabel j) (previous.relabel j)
    (node.relabel j) (seedRank.relabel j) nodeRank hij hrj hpj hmj hn
  exact PrimaryFiniteDescent.ArithmeticProof.budgetStep (depth.relabel j) nodeRank (childRank.relabel j) (seedRank.relabel j)
    (edgeDescent n (node.relabel j) (child.relabel j) (param.relabel j) nodeRank (childRank.relabel j) hej hn hcj) hb

theorem successorAt (n : Nat) (depth seed param frontier child seedRank childRank previous : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount n depth)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R childRank child param)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) previous depth seed param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  have hw := ExchangeFrontierWitness.Proof.successorWitness body alpha Delta OriginalEnumerationRecursionInterface.D
    depth seed param previous frontier child hp hf hm
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness (ExchangeFrontierWitness.dependencyEdge OriginalEnumerationRecursionInterface.D)
    previous child param _ hw
  intro beta j Theta node hj hmem hedge
  simp only [resultRename,sucRelabel]
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  rw [atCountRename] at hij
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hpj
  exact successorNode n (depth.relabel j) (seed.relabel j) (param.relabel j) (previous.relabel j)
    node (child.relabel j) (seedRank.relabel j) (childRank.relabel j) hij hrj hpj hmem hedge hcj

theorem successorCore (n : Nat) (depth seed param frontier child seedRank childRank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount n depth)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R childRank child param)))
    : Nonempty (Derivation body Delta (result (suc depth) seedRank childRank)) := by
  apply programCases (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D)
    (Fin.cons depth (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta previous hj hp
  simp only [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  rw [atCountRename] at hij
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  exact successorAt n (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j)
    (child.relabel j) (seedRank.relabel j) (childRank.relabel j) previous hij hrj hfj hmj hcj hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.FrontierRank.CoreProof
