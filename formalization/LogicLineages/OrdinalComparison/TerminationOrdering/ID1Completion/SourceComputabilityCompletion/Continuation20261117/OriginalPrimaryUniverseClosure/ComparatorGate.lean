module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.ComparatorGate
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

theorem exactPrimaryUniverseClosure : Targets.InternalPrimaryUniverseClosure ↔
    (∀ (n : Nat) (arity : Fin n → Nat)
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
      false targetType targetRaw gamma context))) := Iff.rfl

/-- The internal reached invariant binds candidate, type and raw code. -/
theorem exactAllAccepted {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached gamma context : OTerm alpha) :
    allAccepted n arity reached gamma context =
      InternalClosedPrograms.allBlock
        ((graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1)
            (reached.relabel Sum.inl) (.var (.inr (0 : Fin 3))) ⊓
          graph2 InternalPairing.pairing (.var (.inr (0 : Fin 3)))
            (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))).imp
          (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
            (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
            false (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))
            (gamma.relabel Sum.inl) (context.relabel Sum.inl))) := rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.ComparatorGate
