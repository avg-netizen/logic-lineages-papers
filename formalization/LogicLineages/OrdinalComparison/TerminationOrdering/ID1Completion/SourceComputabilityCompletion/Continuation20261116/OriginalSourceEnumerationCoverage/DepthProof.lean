module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.DepthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sourceDepth (n : Nat) (H : Program 1) (M W : Program 2)
    (typ raw gamma context pair size label bound : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma context)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc bound)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationMembership.Targets.depthBound n raw (add bound bound))) := by
  have ht := OriginalTransparentDecoderValidatorCollapseInclusionProof.termSourceToTarget H M W typ raw gamma context ha
  apply InternalAcceptanceSupportProof.programCases (OriginalEnumerationDepth.depth n) (Fin.cons raw Fin.elim0) _
  intro beta j Theta depth hj hd
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hd
  rw [OriginalEnumerationMembership.DepthSyntaxProof.boundRename,addRelabel]
  have htj := renameInto ht j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  rw [OriginalTypedDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at htj
  rw [graph1Rename] at hbj
  rw [graph2Rename] at hpj
  simp only [ArgumentEntriesDependencyDescent.SupportProof.strictRename,sucRelabel] at hsj
  have hdepth := OriginalTypedEnumerationDepthBound.Proof.internalTerm n H body beta Theta
    (typ.relabel j) (raw.relabel j) (gamma.relabel j) (pair.relabel j) (size.relabel j) (label.relabel j) depth htj hbj hpj hd
  exact OriginalEnumerationMembership.DepthBoundProof.introduce n (raw.relabel j) (add (bound.relabel j) (bound.relabel j)) depth hd
    (OriginalTypedEnumerationDepthBound.ArithmeticProof.termMonotone depth (size.relabel j) (bound.relabel j) hdepth hsj)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.DepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.DepthProof
