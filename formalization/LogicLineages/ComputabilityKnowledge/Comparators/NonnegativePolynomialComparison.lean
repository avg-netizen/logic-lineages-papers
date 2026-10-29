module

public import LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison

@[expose] public section

/-! Independent full well-formed nonnegative-code semantic reduction. It has
no undecidability premise. Both counterexamples and universal comparisons use
the same explicit finite positive output domain, including arity-zero sources. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparison

open PositiveExpression PolynomialCircuit PolynomialDomainShift
open LogicLineages.ComputabilityKnowledge.NonnegativePolynomialComparison
open CircuitComparison (finiteVal)

def FixedInputs : Prop :=
  ∀ p : Code, p.WellFormed → ∀ ν : Fin p.inputCount → Nat,
    evalNonnegative p ν = 0 ↔ ∃ τ : Fin (bound p) → PosNat,
      AgreesShiftedInputs p ν τ ∧ (upper p).eval (finiteVal τ) = (lower p).eval (finiteVal τ)

def EqualityWitness : Prop :=
  ∀ p : Code, p.WellFormed →
    (HasNonnegativeRoot p ↔ ∃ τ : Fin (bound p) → PosNat,
      (upper p).eval (finiteVal τ) = (lower p).eval (finiteVal τ))

def RootCounterexamples : Prop :=
  ∀ p : Code, p.WellFormed →
    (HasNonnegativeRoot p ↔ ∃ τ : Fin (bound p) → PosNat,
      ¬ (lower p).eval (finiteVal τ) < (upper p).eval (finiteVal τ)) ∧
    (HasNonnegativeRoot p ↔ ∃ τ : Fin (bound p) → PosNat,
      ¬ (weakLower p).eval (finiteVal τ) ≤ (upper p).eval (finiteVal τ))

def StrictReduction : Prop :=
  ∀ p : Code, p.WellFormed →
    (¬ HasNonnegativeRoot p ↔ ∀ τ : Fin (bound p) → PosNat,
      (lower p).eval (finiteVal τ) < (upper p).eval (finiteVal τ))

def WeakReduction : Prop :=
  ∀ p : Code, p.WellFormed →
    (¬ HasNonnegativeRoot p ↔ ∀ τ : Fin (bound p) → PosNat,
      (weakLower p).eval (finiteVal τ) ≤ (upper p).eval (finiteVal τ))

def CircuitContract : Prop :=
  ∀ p : Code, p.WellFormed → (circuit p).inputCount = p.inputCount ∧
    (circuit p).WellFormed ∧ 2 ≤ (circuit p).gates.length ∧
      bound p = p.inputCount + 9 * (circuit p).gates.length

def AlwaysOrdered : Prop :=
  ∀ p : Code, p.WellFormed → ∀ τ : Fin (bound p) → PosNat,
    (lower p).eval (finiteVal τ) ≤ (upper p).eval (finiteVal τ)

def DepthBound : Prop :=
  ∀ p : Code, p.WellFormed → (upper p).depth ≤ 2 ∧ (lower p).depth ≤ 2 ∧ (weakLower p).depth ≤ 2

def VariablesBounded : Prop :=
  ∀ p : Code, p.WellFormed →
    CircuitReduction.Bounded (bound p) (upper p) ∧ CircuitReduction.Bounded (bound p) (lower p) ∧
      CircuitReduction.Bounded (bound p) (weakLower p)

def Target : Prop := FixedInputs ∧ EqualityWitness ∧ RootCounterexamples ∧ StrictReduction ∧
  WeakReduction ∧ CircuitContract ∧ AlwaysOrdered ∧ DepthBound ∧ VariablesBounded

end LogicLineages.ComputabilityKnowledge.Comparators.NonnegativePolynomialComparison
