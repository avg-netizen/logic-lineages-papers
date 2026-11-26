module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ComparatorGate
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

theorem exactPrimaryVariableRankPreservation : Targets.InternalPrimaryVariableRankPreservation ↔
    (∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out candidate seedType seedRaw targetType targetRaw seedRank targetRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)) →
  Nonempty (Derivation body Delta
    (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw seedRank seed)) →
  Nonempty (Derivation body Delta
    (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw targetRank candidate)) →
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
    (eqn seedRank targetRank))) := Iff.rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ComparatorGate
