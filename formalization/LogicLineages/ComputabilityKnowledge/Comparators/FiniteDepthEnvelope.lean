module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelope
open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope

def LiteralAffineConstruction : Prop :=
  ∀ e : Expr Nat, 0 < nodeCount e ∧ (variableList e).Nodup ∧
    (∀ i, i ∈ variableList e ↔ i ∈ rawVariables e) ∧
    (s0 e).depth = 0 ∧ (bTerm e).depth = 0 ∧ (envelope e).depth = 0 ∧
    ∀ ρ : Nat → PosNat,
      (s0 e).eval ρ = 1 + ((variableList e).map (fun i => (ρ i).val)).sum ∧
      (bTerm e).eval ρ = (nodeCount e+1)*(s0 e).eval ρ ∧
      (envelope e).eval ρ = 5*(bTerm e).eval ρ ∧
      0 < (s0 e).eval ρ ∧ 0 < (bTerm e).eval ρ ∧ 0 < (envelope e).eval ρ

def SameVariables : Prop :=
  ∀ (d : Nat) (e : Expr Nat), Bounded d (envelope e) ↔ Bounded d e

def DepthTwoBound : Prop :=
  ∀ (e : Expr Nat), e.depth ≤ 2 → ∀ ρ : Nat → PosNat,
    e.eval ρ ≤ 2 ^ (2 ^ (envelope e).eval ρ)

def Target : Prop := LiteralAffineConstruction ∧ SameVariables ∧ DepthTwoBound
end LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthEnvelope
