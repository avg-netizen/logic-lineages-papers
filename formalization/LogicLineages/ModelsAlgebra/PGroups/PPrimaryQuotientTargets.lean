module
public import Mathlib.GroupTheory.QuotientGroup.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupPPrimaryQuotient : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (T : AddSubgroup G),
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) →
    ∀ x : G ⧸ T, ∃ n : ℕ, p^n • x = 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
