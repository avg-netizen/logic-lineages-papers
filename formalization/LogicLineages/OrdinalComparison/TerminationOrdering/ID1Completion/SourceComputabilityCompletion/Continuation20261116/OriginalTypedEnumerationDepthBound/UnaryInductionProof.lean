module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildObservationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andLeft)
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem weakenMode (arguments : Bool) (size depth : OTerm alpha)
    (h : Nonempty (Derivation body Delta (result arguments size depth))) :
    Nonempty (Derivation body Delta (argumentsBound depth size)) := by
  cases arguments
  · exact ArithmeticProof.termToArguments depth size (andLeft h)
  · exact h

theorem step (ordinary : Bool) (n : Nat) (H : Program 1)
    (raw metadata child pair size label depth childTyp childGamma : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsConstructors.UnaryValueProof.constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (hsmall : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hgc : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) child)))
    (ht : Nonempty (Derivation body Delta (accepted H ordinary childTyp child childGamma))) :
    Nonempty (Derivation body Delta (result false size depth)) := by
  apply ChildObservationsProof.cases n child (result false size depth)
  intro beta j Theta childPair childSize childLabel childDepth hj hcb hcp hcd
  rw [SyntaxProof.resultRename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hbj := renameInto hb j Theta hj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have ihj := renameInto ih j Theta hj
  have hsmallj := renameInto hsmall j Theta hj
  have hgcj := renameInto hgc j Theta hj
  have htj := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hcj hgj hbj hpj hdj hgcj
  rw [InductionSyntaxProof.belowRawRename] at ihj
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hsmallj
  rw [SyntaxProof.acceptedRename] at htj
  have hi := ChildInductionProof.childResult n H ordinary (raw.relabel j) (child.relabel j)
    (childTyp.relabel j) (childGamma.relabel j) childPair childSize childLabel childDepth
    ihj hsmallj hgcj htj hcb hcp hcd
  exact UnaryClosureProof.value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j)
    (pair.relabel j) (size.relabel j) (label.relabel j) (depth.relabel j)
    childPair childSize childLabel childDepth hcj hgj hbj hpj hdj hcb hcp hcd
    (weakenMode ordinary childSize childDepth hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryInductionProof
