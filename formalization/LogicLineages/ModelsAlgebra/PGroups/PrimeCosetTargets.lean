module
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupPrimeCosetOrder : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (B : AddSubgroup G) (x : G),
    x ∉ B → p • x ∈ B → addOrderOf ((QuotientAddGroup.mk' B) x) = p

def groupPrimeCosetIntegerMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (B : AddSubgroup G) (x : G),
    x ∉ B → p • x ∈ B → ∀ z : ℤ, z • x ∈ B ↔ (p : ℤ) ∣ z

end LogicLineages.ModelsAlgebra.PGroups.Targets
