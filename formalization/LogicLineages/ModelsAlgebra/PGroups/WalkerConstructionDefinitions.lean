module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamilyUlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual group nature, with no asserted classification invariant. -/
def WalkerConstructedGroupNature (p : ℕ) (G : Type) [AddCommGroup G] : Prop :=
  Countable G ∧ (∀ x : G, ∃ n : ℕ, p^n • x = 0) ∧
    ∀ S : AddSubgroup G, (∀ n : ℕ, n ≠ 0 → ∀ x : S, ∃ y : S, n • y = x) → S = ⊥
/-- Length means the actual first zero filtration stage. -/
def WalkerExactLength (p : ℕ) (G : Type) [AddCommGroup G] (ell : Ordinal.{0}) : Prop :=
  (transfiniteFiltration p ell : AddSubgroup G) = ⊥ ∧
    ∀ α < ell, (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥
end LogicLineages.ModelsAlgebra.PGroups
