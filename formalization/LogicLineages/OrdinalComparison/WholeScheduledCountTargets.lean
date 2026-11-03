module
public import LogicLineages.OrdinalComparison.WholeScheduledCountDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WholeScheduledCount.Targets

def ExactRecursion : Prop :=
  ∀ b : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    (a < Ordinal.omega0 → count b a = 0) ∧
    (Ordinal.omega0 ≤ a → count b a =
      count (fun i => b (i+1)) (actualMaximumPredecessor a (b 0)) + 1)

def FirstFinite : Prop :=
  ∀ b : Nat → Nat, ∀ a : Ordinal.{0}, a < epsilonZero →
    stateAfter b a (count b a) < Ordinal.omega0 ∧
    ∀ i : Nat, i ≤ count b a →
      stateAfter b a i < epsilonZero ∧ stateAfter b a i ≤ a ∧
      (i < count b a → Ordinal.omega0 ≤ stateAfter b a i)

def UniformLinearLowerBound : Prop :=
  ∀ q : Nat, ∀ b : Nat → Nat, ∀ a : Ordinal.{0},
    Ordinal.omega0 * (q : Ordinal) ≤ a → a < epsilonZero →
    (∀ i : Nat, 2*q ≤ b i) → q ≤ count b a
end LogicLineages.OrdinalComparison.WholeScheduledCount.Targets
