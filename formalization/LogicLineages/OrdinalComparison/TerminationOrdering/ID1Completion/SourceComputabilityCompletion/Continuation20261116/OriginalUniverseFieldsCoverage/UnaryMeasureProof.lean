module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.BoundsMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.UnaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem atPair (ordinary : Bool) (n : Nat)
    (raw metadata child pair size label childPair childSize childLabel canonical : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalCodeBoundsConstructors.UnaryValueProof.constructor ordinary) raw metadata child)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hcb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) childPair child)))
    (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPair childSize childLabel)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc childSize) childLabel))) :
    Nonempty (Derivation body Delta (eqn size (suc childSize) ⊓ eqn label childLabel)) := by
  have hv := OriginalCodeBoundsConstructors.UnaryValueProof.value ordinary n raw metadata child
    childPair childSize childLabel canonical hc hg hcb hcp hk
  exact andIntro (BoundsMeasureProof.measuredSize n raw pair size label canonical (suc childSize) childLabel hb hp hv hk)
    (BoundsMeasureProof.measuredLabel n raw pair size label canonical (suc childSize) childLabel hb hp hv hk)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
