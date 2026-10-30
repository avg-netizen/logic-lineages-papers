module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizer

@[expose] public section

/-! Exact mathematical normalization supplier for paper 02, (N1)/(N2).
The input is the unchanged literal positive-expression grammar and depth.
The output must be an actual well-formed finite hereditary map with its
literal sum semantics. This does not assert effective extraction of a
finite numerical code, extensional completeness, or a decision algorithm.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizer

open PositiveExpression ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialNormalizer

def Variables : Prop :=
  ∀ (d h : Nat) (i : Fin d) (ρ : Fin d → Nat),
    value h (variableForm h i) ρ = ρ i ∧
    constantCoefficient h (variableForm h i) = 0 ∧
    WellFormed h (variableForm h i)

def BoundedNormalization : Prop :=
  ∀ (d : Nat) (a : Expr (Fin d)) (h : Nat), a.depth ≤ h →
    WellFormed h (normalizeAt a h) ∧
    ∀ ρ : Fin d → PosNat,
      value h (normalizeAt a h) (fun i => (ρ i : Nat)) = a.eval ρ

def SourceNormalization : Prop :=
  ∀ (d : Nat) (a : Expr (Fin d)),
    WellFormed a.depth (normalize a) ∧
    ∀ ρ : Fin d → PosNat,
      value a.depth (normalize a) (fun i => (ρ i : Nat)) = a.eval ρ

def Target : Prop := Variables ∧ BoundedNormalization ∧ SourceNormalization

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizer
