module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

/-- Actual endpoint hypotheses bundled for internal query elimination only.
There is no metadata or target-admission field. -/
structure Request {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (Delta : List (Formula alpha))
    (seed parameter out candidate seedQ targetQ : OTerm alpha) where
  admitted : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter))
  primary : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (OriginalConcreteStructuralEdge.edge n arity)) out seed parameter))
  member : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out candidate))
  sourceCandidates : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) seedQ seed parameter))
  targetCandidates : Nonempty (Derivation body Delta (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) targetQ candidate parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting
