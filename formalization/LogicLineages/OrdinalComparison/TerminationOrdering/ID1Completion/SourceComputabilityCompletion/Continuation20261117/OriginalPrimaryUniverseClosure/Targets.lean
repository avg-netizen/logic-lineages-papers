module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- The actual installed original primary output preserves universe acceptance
from its admitted seed, with the same parameter/context/Gamma. No target
acceptance, reached invariant, pool membership or arbitrary edge oracle is a
premise. The candidate type is its own observed type, not assumed equal to the
seed type. This is an internal preservation law, not global accessibility. -/
def InternalPrimaryUniverseClosure : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate seedType seedRaw targetType targetRaw context gamma : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
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
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false seedType seedRaw gamma context)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false targetType targetRaw gamma context))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Targets
