module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafIntrinsicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafCapacityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafProof
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

theorem variableCode (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw field : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw field)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs))) :
    Nonempty (Derivation body Delta (result n false raw xs)) :=
  andIntro (LeafIntrinsicProof.variableCode n raw field (xs 8) (xs 9) (xs 10) hc
    (ObservationPartsProof.bounds n arity H false raw xs ho)
    (ObservationPartsProof.pairing n arity H false raw xs ho))
    (LeafCapacityProof.variableCode n arity H raw field xs hc ho)

theorem bottom (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw field : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw field)))
    (ho : Nonempty (Derivation body Delta (observations n arity H false raw xs))) :
    Nonempty (Derivation body Delta (result n false raw xs)) :=
  andIntro (LeafIntrinsicProof.bottom n raw field (xs 8) (xs 9) (xs 10) hc
    (ObservationPartsProof.bounds n arity H false raw xs ho)
    (ObservationPartsProof.pairing n arity H false raw xs ho))
    (LeafCapacityProof.bottom n arity H raw field xs hc ho)

theorem nilCode (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta (observations n arity H true raw xs))) :
    Nonempty (Derivation body Delta (result n true raw xs)) :=
  andIntro (LeafIntrinsicProof.nilCode n arity H raw (xs 5) (xs 6) (xs 2) (xs 3) (xs 9) hc
    (ObservationPartsProof.admission n arity H true raw xs ho))
    (LeafCapacityProof.nilCode n raw xs hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.LeafProof
