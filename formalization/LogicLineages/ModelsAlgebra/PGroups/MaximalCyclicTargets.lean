module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

/-- Actual root correction in a maximal-order cyclic subgroup of a bounded
group. This asserts neither a projection nor a cyclic decomposition. -/
def groupMaximalCyclicRootCorrection : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (G : Type u) [AddCommGroup G],
    (∀ z : G, p ^ k • z = 0) → ∀ y : G, addOrderOf y = p ^ k →
    ∀ (n : ℕ) (x : G) (a : ℤ), p ^ n • x = a • y →
      ∃ b : ℤ, p ^ n • x = p ^ n • (b • y)

end LogicLineages.ModelsAlgebra.PGroups.Targets
