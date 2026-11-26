module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import Mathlib.Order.Monotone.Basic
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullHierarchyGrowth.Targets
open LogicLineages.OrdinalComparison

def CompleteGrowth : Prop :=
  (∀ j : Nat, StrictMono (fastControl j)) ∧
  (∀ j n : Nat, n < fastControl j n) ∧
  (∀ j n : Nat, 1 ≤ n → 2 ^ n ≤ fastControl j n) ∧
  (∀ n : Nat, ∃ k : Nat, Phi n = 2 ^ k) ∧
  (∀ n : Nat, 2 ^ (n + 100) ≤ Phi n) ∧
  (∀ n : Nat, 2 ^ (Phi n + 1) ≤ Phi (n + 1))
end LogicLineages.CartierObserverCurrent.FullHierarchyGrowth.Targets
