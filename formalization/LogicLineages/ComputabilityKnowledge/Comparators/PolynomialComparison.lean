module

public import LogicLineages.ComputabilityKnowledge.PolynomialComparison

@[expose] public section

/-! Independent semantic target for the entire positive-code construction.
No polynomial-root oracle or supplier premise is present. Every output uses
one shared Fin(bound) positive valuation; inputs are fixed in FixedInputs. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparison

open PositiveExpression PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.PolynomialComparison
open CircuitComparison (finiteVal)

def FixedInputs : Prop :=
  ∀ p : Code, p.WellFormed → ∀ ρ : Fin p.inputCount → PosNat,
    evalAt p ρ = 0 ↔ ∃ τ : Fin (bound p) → PosNat,
      AgreesInputs p ρ τ ∧ (upper p).eval (finiteVal τ) = (lower p).eval (finiteVal τ)

def EqualityWitness : Prop :=
  ∀ p : Code, p.WellFormed →
    (HasPositiveRoot p ↔ ∃ τ : Fin (bound p) → PosNat,
      (upper p).eval (finiteVal τ) = (lower p).eval (finiteVal τ))

def StrictReduction : Prop :=
  ∀ p : Code, p.WellFormed →
    (¬ HasPositiveRoot p ↔ ∀ τ : Fin (bound p) → PosNat,
      (lower p).eval (finiteVal τ) < (upper p).eval (finiteVal τ))

def WeakReduction : Prop :=
  ∀ p : Code, p.WellFormed →
    (¬ HasPositiveRoot p ↔ ∀ τ : Fin (bound p) → PosNat,
      (weakLower p).eval (finiteVal τ) ≤ (upper p).eval (finiteVal τ))

def AlwaysOrdered : Prop :=
  ∀ p : Code, p.WellFormed → ∀ τ : Fin (bound p) → PosNat,
    (lower p).eval (finiteVal τ) ≤ (upper p).eval (finiteVal τ)

def DepthBound : Prop :=
  ∀ p : Code, p.WellFormed → (upper p).depth ≤ 2 ∧ (lower p).depth ≤ 2 ∧ (weakLower p).depth ≤ 2

def VariablesBounded : Prop :=
  ∀ p : Code, p.WellFormed →
    CircuitReduction.Bounded (bound p) (upper p) ∧ CircuitReduction.Bounded (bound p) (lower p) ∧
      CircuitReduction.Bounded (bound p) (weakLower p)

def Target : Prop := FixedInputs ∧ EqualityWitness ∧ StrictReduction ∧ WeakReduction ∧
  AlwaysOrdered ∧ DepthBound ∧ VariablesBounded

end LogicLineages.ComputabilityKnowledge.Comparators.PolynomialComparison
