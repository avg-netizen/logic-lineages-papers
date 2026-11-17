module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Re-root the literal candidate LIST at an actual admitted-primary member.
The same parameter, concrete H, original Q and E are retained. No equal
metadata or candidate-list premise, no universe predicate, native calibration,
external reachability or pool equality is supplied. -/
def InternalCandidateRerooting : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate seedQ targetQ : OTerm alpha),
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
    (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))
      seedQ seed parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))
      targetQ candidate parameter)) →
  Nonempty (Derivation body Delta (eqn seedQ targetQ))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.Targets
