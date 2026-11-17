module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Equality of literal original PRE-rankguard minima at an actual original primary member.
Original source scope and observed primary outputs retained; only the two actual
minimum output graphs are added. No postguard or final presentation claim. -/
def InternalMinimumCoherence : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter typ raw context gamma types out candidate targetOut minimumOut targetMinimumOut : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
  Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed parameter)) →
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (OriginalUniverseDecoderInternalAcceptance.TermAccepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) out seed parameter)) →
  Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate)) →
  Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) targetOut candidate parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTransparentMinimum.minimum (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (TwoSol20261113.CalibratedPrimary.Membership.classTest (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) (TransparentCandidate.candidate (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))))) minimumOut seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (OriginalTransparentMinimum.minimum (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (TwoSol20261113.CalibratedPrimary.Membership.classTest (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) (TransparentCandidate.candidate (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))))) targetMinimumOut candidate parameter)) →
  Nonempty (Derivation body Delta (equal minimumOut targetMinimumOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Targets
