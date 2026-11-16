module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.LeafMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ConstructorArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.UnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (valueUnique)
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atPair (ordinary : Bool) (n : Nat)
    (raw metadata child pair size label depth childPair childSize childLabel childDepth canonical : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsConstructors.UnaryValueProof.constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw)))
    (hcb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) childPair child)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPair childSize childLabel)))
    (hcd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) childDepth child)))
    (hcanonical : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc childSize) childLabel)))
    (hbound : Nonempty (Derivation body Delta (argumentsBound childDepth childSize))) :
    Nonempty (Derivation body Delta (termBound depth size ⊓ InternalLessThan.strictLess z size)) := by
  have hvalue := OriginalCodeBoundsConstructors.UnaryValueProof.value ordinary n raw metadata child
    childPair childSize childLabel canonical hc hg hcb hcp hcanonical
  have hs := LeafMeasureProof.measuredSize n raw pair size label canonical (suc childSize) childLabel hb hp hvalue hcanonical
  have hdepth := OriginalEnumerationDepth.UnaryProof.value ordinary n raw metadata child childDepth hc hg hcd
  have he := valueUnique (OriginalEnumerationDepth.depth n) depth (suc childDepth) ![raw] hd hdepth
  exact ConstructorArithmeticProof.unary childSize childDepth size depth hs he hbound
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.UnaryMeasureProof
