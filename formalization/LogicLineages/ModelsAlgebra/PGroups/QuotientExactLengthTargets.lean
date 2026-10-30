module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupQuotientExactLength : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (K T : AddSubgroup G) (N : ℕ),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T → 0 < N →
    (∀ x : (transfiniteFiltration p δ : AddSubgroup G), p^N • x = 0) →
    (∃ x : K, p^(N-1) • x ≠ 0) →
    ((transfiniteFiltration p (δ+(N : Ordinal.{v})) : AddSubgroup G) = ⊥ ∧
      (transfiniteFiltration p (δ+(N : Ordinal.{v})) : AddSubgroup (G ⧸ T)) = ⊥) ∧
    ∀ α < δ+(N : Ordinal.{v}),
      (transfiniteFiltration p α : AddSubgroup G) ≠ ⊥ ∧
      (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) ≠ ⊥

end LogicLineages.ModelsAlgebra.PGroups.Targets
