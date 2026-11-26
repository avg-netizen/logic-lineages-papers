module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- One literal installed edge into the actual filtered seed pool. Seed admission is
explicit; target admission, both Code guards and the unchanged runtime environment
are derived. No arbitrary structural supplier or reached-list invariant is assumed. -/
def InternalInstalledFilteredEdgeUniverse : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter pool source target sourceType sourceRaw targetType targetRaw context gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
      (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
      (OriginalDecodedContextValidity.contextGuard n))
      (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool target)) →
  Nonempty (Derivation body Delta
    (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false sourceType sourceRaw gamma context)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false targetType targetRaw gamma context))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Targets
