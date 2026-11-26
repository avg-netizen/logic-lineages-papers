module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Actual original raw exchange preserves all-variable-occurrence rank under
both original Code guards. Rank graphs are observed independently; no equality,
permutation sum, source typing, native calibration, or semantic exchange oracle
is supplied. No malformed-input claim or numeric-size identification. -/
def InternalRawExchangeVariableRank : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right node window leftRank rightRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) left)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) right)) →
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw leftRank left)) →
  Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rightRank right)) →
  Nonempty (Derivation body Delta (eqn leftRank rightRank))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Targets
