module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelopeEffectivity
open PositiveExpression CircuitReduction FiniteComparisonEnumeration
open LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope

def Target : Prop :=
  Computable (fun p : Nat × List Nat => envelopeCode p.1 p.2) ∧
  (∀ (d : Nat) (e : Expr Nat), Bounded d e →
    envelopeCode d (encodeExpr e) = some (encodeExpr (envelope e))) ∧
  (∀ (d : Nat) (xs : List Nat), envelopeCode d xs = none ↔ decodeExpr d xs = none) ∧
  (∀ (d : Nat) (e : Expr Nat), Bounded d e →
    decodeExpr d (encodeExpr (envelope e)) = some (envelope e))
end LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelopeEffectivity
