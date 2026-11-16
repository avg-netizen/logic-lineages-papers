module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem value (ordinary : Bool) (n : Nat)
    (raw metadata child pair size label depth childPair childSize childLabel childDepth : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsConstructors.UnaryValueProof.constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (hcb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) childPair child)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPair childSize childLabel)))
    (hcd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) childDepth child)))
    (hbound : Nonempty (Derivation body Delta (argumentsBound childDepth childSize))) :
    Nonempty (Derivation body Delta (termBound depth size ⊓ InternalLessThan.strictLess z size)) := by
  change Nonempty (Derivation body Delta (Induction.result false size depth))
  change Nonempty (Derivation body Delta (Induction.result true childSize childDepth)) at hbound
  apply programCases InternalPairing.pairing (Fin.cons (suc childSize) (Fin.cons childLabel Fin.elim0)) _
  intro beta j Theta canonical hj hcanonical
  simp only [consTermRename,emptyRename,sucRelabel] at hcanonical
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hcbj := renameInto hcb j Theta hj
  have hcpj := renameInto hcp j Theta hj
  have hcdj := renameInto hcd j Theta hj
  have hboundj := renameInto hbound j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hcj hgj hbj hpj hdj hcbj hcpj hcdj
  rw [SyntaxProof.resultRename] at hboundj
  exact UnaryMeasureProof.atPair ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j)
    (childPair.relabel j) (childSize.relabel j) (childLabel.relabel j) (childDepth.relabel j) canonical
    hcj hgj hbj hpj hdj hcbj hcpj hcdj hcanonical hboundj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryClosureProof
