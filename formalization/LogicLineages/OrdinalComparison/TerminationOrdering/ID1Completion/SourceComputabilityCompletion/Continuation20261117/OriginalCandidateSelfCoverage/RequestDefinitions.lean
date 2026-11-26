module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc)
structure Request {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (Delta : List (Formula alpha))
    (seed parameter typ raw context gamma types out : OTerm alpha) where
  seedPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw))
  parameterPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma))
  guard : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context))
  typesGraph : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed parameter))
  closed : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))
  accepted : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context))
  candidates : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity H) out seed parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage
