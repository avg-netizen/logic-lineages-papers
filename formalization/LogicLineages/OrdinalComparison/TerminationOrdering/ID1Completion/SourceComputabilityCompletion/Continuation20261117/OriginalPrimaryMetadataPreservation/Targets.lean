module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- An actual member of the literal original primary output retains the seed's
observed root type and complete original (size,maxLabel) bounds pair. Both
packed field pairs and bounds outputs are independent observations, not assumed
equal. No universe acceptance, target admission, target pool membership,
reached invariant, arbitrary edge supplier or external reachability premise. -/
def InternalPrimaryMetadataPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate seedType seedRaw targetType targetRaw seedBounds targetBounds : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalCodeBoundsRecursion.bounds n) seedBounds seedRaw)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalCodeBoundsRecursion.bounds n) targetBounds targetRaw)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
      (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (SeededPrimaryPool.primary
      (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
        (OriginalDecodedContextValidity.contextGuard n))
      (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))
      (OriginalConcreteStructuralEdge.edge n arity)) out seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta
    (eqn seedType targetType ⊓ eqn seedBounds targetBounds))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Targets
