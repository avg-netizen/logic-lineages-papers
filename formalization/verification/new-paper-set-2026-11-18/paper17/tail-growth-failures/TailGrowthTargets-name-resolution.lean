module
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Complete Paper17 lem:tail-growth, without an eventual input restriction. -/
def FixedHeadTailGrowth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam → ∀ u : Nat,
      2 ^ collapseWith f (lam + (u : Ordinal)) <
        collapseWith f (lam + ((u + 1 : Nat) : Ordinal))

/-- The two literal source controls, explicitly including every prefix input. -/
def ConcreteFixedHeadTailGrowth : Prop :=
  (∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam → ∀ u : Nat,
    2 ^ collapseWith factorialControl (lam + (u : Ordinal)) <
      collapseWith factorialControl (lam + ((u + 1 : Nat) : Ordinal))) ∧
  (∀ b : Nat, ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam → ∀ u : Nat,
    2 ^ collapseWith (nearControl b) (lam + (u : Ordinal)) <
      collapseWith (nearControl b) (lam + ((u + 1 : Nat) : Ordinal)))

def FullTailGrowth : Prop := FixedHeadTailGrowth ∧ ConcreteFixedHeadTailGrowth

end LogicLineages.PermittedControl.Targets
