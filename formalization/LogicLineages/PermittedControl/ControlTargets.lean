module
public import LogicLineages.PermittedControl.FactorialDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- Literal clauses of paper17 lem:control for a chosen numerical control
and its stated threshold. This is a proposition to be proved, not an oracle. -/
def ControlLaws (f : Nat → Nat) (B : Nat) : Prop :=
  (∀ (n : Nat), 2 ∣ f n) ∧
  Primrec f ∧
  (∀ (n : Nat), G n ≤ f n) ∧
  (∀ (n : Nat), 2 ^ (2 ^ f n) ≤ f (n + 1)) ∧
  (∀ (n : Nat), f n < G (n + 1)) ∧
  (∃ (j N : Nat), ∀ (n : Nat), N ≤ n → f n ≤ OrdinalComparison.fastControl j n) ∧
  (∀ (m n : Nat), 0 < m → max m B ≤ n →
    Int.ModEq (m : Int) (potential (f n) : Int) ((potential n : Int) - 1))

/-- Both actual source controls, not merely a conditional generic theorem. -/
def FullControl : Prop :=
  ControlLaws factorialControl 0 ∧ ∀ (b : Nat), ControlLaws (nearControl b) (b + 1)

/-- The same explicit finite level and threshold work uniformly for both
controls and every preserved finite prefix. -/
def UniformFiniteLevel : Prop :=
  ∃ (j N : Nat), (∀ (n : Nat), N ≤ n → factorialControl n ≤ OrdinalComparison.fastControl j n) ∧
    (∀ (b n : Nat), N ≤ n → nearControl b n ≤ OrdinalComparison.fastControl j n)

end LogicLineages.PermittedControl.Targets
