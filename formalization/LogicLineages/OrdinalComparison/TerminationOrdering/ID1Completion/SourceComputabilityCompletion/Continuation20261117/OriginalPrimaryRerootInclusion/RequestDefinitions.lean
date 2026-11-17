module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.RequestRenameProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
structure Request (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    {alpha : Type} (Delta : List (Formula alpha))
    (seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha) : Prop where
  seedPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed typ raw))
  parameterPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma))
  guard : Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context))
  typesGraph : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed parameter))
  closed : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))
  accepted : Nonempty (Derivation body Delta
    (OriginalUniverseDecoderInternalAcceptance.TermAccepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context))
  primary : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) out seed parameter))
  member : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate))
  targetPrimary : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) targetOut candidate parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion
