module

public import LogicLineages.ComputabilityKnowledge.CircuitComparison

@[expose] public section

/-! Independent finite-domain comparison target. Both sides always share the
same Fin(d) positive valuation. The fixed-input clause retains original inputs;
no separate witnesses for the two terms or unrestricted valuation is substituted.
The retained output equation handles empty gate lists exactly as in the source. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparison

open PositiveExpression CircuitReduction
open LogicLineages.ComputabilityKnowledge.CircuitComparison

def FixedInputs : Prop :=
  ∀ c : Circuit, c.WellFormed → ∀ ρ : Fin c.inputCount → PosNat,
    c.outputEqual (finiteVal ρ) ↔
      ∃ τ : Fin (variableBound c) → PosNat, AgreesInputs c ρ τ ∧
        (upper c).eval (finiteVal τ) = (lower c).eval (finiteVal τ)

def EqualityWitness : Prop :=
  ∀ c : Circuit, c.WellFormed →
    (Solvable c ↔ ∃ τ : Fin (variableBound c) → PosNat,
      (upper c).eval (finiteVal τ) = (lower c).eval (finiteVal τ))

def StrictReduction : Prop :=
  ∀ c : Circuit, c.WellFormed →
    (¬ Solvable c ↔ ∀ τ : Fin (variableBound c) → PosNat,
      (lower c).eval (finiteVal τ) < (upper c).eval (finiteVal τ))

def WeakReduction : Prop :=
  ∀ c : Circuit, c.WellFormed →
    (¬ Solvable c ↔ ∀ τ : Fin (variableBound c) → PosNat,
      (weakLower c).eval (finiteVal τ) ≤ (upper c).eval (finiteVal τ))

def AlwaysOrdered : Prop :=
  ∀ c : Circuit, c.WellFormed → ∀ τ : Fin (variableBound c) → PosNat,
    (lower c).eval (finiteVal τ) ≤ (upper c).eval (finiteVal τ)

def DepthBound : Prop :=
  ∀ c : Circuit, c.WellFormed →
    (upper c).depth ≤ 2 ∧ (lower c).depth ≤ 2 ∧ (weakLower c).depth ≤ 2

def VariablesBounded : Prop :=
  ∀ c : Circuit, c.WellFormed →
    Bounded (variableBound c) (upper c) ∧ Bounded (variableBound c) (lower c) ∧
      Bounded (variableBound c) (weakLower c)

def Target : Prop := FixedInputs ∧ EqualityWitness ∧ StrictReduction ∧
  WeakReduction ∧ AlwaysOrdered ∧ DepthBound ∧ VariablesBounded

end LogicLineages.ComputabilityKnowledge.Comparators.CircuitComparison
