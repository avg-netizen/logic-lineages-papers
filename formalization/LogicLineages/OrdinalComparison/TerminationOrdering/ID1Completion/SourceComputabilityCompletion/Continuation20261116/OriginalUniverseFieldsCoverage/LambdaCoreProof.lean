module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCapacityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.UnaryMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCoreProof
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

open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem atPair (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw domain child childType extended childPair childSize childLabel canonical : OTerm alpha)
    (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (xs 3) domain)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) childPair child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPair childSize childLabel)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing canonical (suc childSize) childLabel)))
    (hchild : Nonempty (Derivation body Delta (result n false child
      (ChildFrameProof.frame xs childType extended (suc (xs 7)) childPair childSize childLabel)))) :
    Nonempty (Derivation body Delta (result n false raw xs)) := by
  have hg := OriginalEnumerationValidity.ChildProof.lambda n raw domain child hc
    (ObservationsProof.intrinsicGuard n false child _ hchild)
  have hmeasure := UnaryMeasureProof.atPair false n raw domain child (xs 8) (xs 9) (xs 10)
    childPair childSize childLabel canonical hc hg
    (ObservationPartsProof.bounds n arity H false raw xs ho)
    (ObservationPartsProof.pairing n arity H false raw xs ho) hb hp hk
  exact andIntro (andIntro hg (CapacityArithmeticProof.unaryPositive (xs 9) childSize (andLeft hmeasure)))
    (LambdaCapacityProof.atChild n raw domain child childType extended childPair childSize childLabel xs
      hc hg hm (andLeft hmeasure) (andRight hmeasure) (ObservationsProof.enclosing n false child _ hchild))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LambdaCoreProof
