module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Internal mutual membership inclusion of actual original primary outputs at
an actual primary member. This is NOT list-code equality or an externally
assumed equivalence relation. Original source scope remains explicit. -/
def InternalPrimaryRerootCoherence : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha),
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
  Nonempty (Derivation body Delta
    (PrimaryMonotonicity.included targetOut out ⊓ PrimaryMonotonicity.included out targetOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Targets
