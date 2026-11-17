module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ComparatorGate
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
theorem exactOriginalRawExchangeVariableRank : Targets.InternalRawExchangeVariableRank ↔
  (∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right node window leftRank rightRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw leftRank left)) →
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rightRank right)) →
  Nonempty (Derivation body Delta (eqn leftRank rightRank))) := Iff.rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ComparatorGate
