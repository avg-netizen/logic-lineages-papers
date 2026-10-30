module
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupPowerStepSelection : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ),
    (∀ y : G, ∃ n : ℕ, p^n • y = 0) → ∀ (B D : AddSubgroup G), B ≤ D → ¬D ≤ B →
      ∃ x : G, x ∈ D ∧ x ∉ B ∧ p • x ∈ B

end LogicLineages.ModelsAlgebra.PGroups.Targets
