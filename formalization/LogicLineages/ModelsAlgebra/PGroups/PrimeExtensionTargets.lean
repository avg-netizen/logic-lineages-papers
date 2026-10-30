module
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupPrimeOrderExtension : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (x : G), x ∉ B → ∀ hpx : p • x ∈ B,
    ∀ (f : B →+ H), Function.Injective f → ∀ w : H,
    w ∉ f.range → p • w = f ⟨p • x,hpx⟩ →
    ∃ F : ↥(B ⊔ AddSubgroup.zmultiples x) →+ H, Function.Injective F ∧
      (∀ b : B, F ⟨b, (le_sup_left : B ≤ B ⊔ AddSubgroup.zmultiples x) b.property⟩ = f b) ∧
      F ⟨x, (le_sup_right : AddSubgroup.zmultiples x ≤ B ⊔ AddSubgroup.zmultiples x)
        (AddSubgroup.mem_zmultiples x)⟩ = w

end LogicLineages.ModelsAlgebra.PGroups.Targets
