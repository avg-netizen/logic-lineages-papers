module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupInternalProjectionExistence : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (K T H : AddSubgroup G)
    (hH : H = K ⊔ T), Disjoint K T →
    ∃ r : H →+ K, ∀ x : K,
      r ⟨x, by rw [hH]; exact (le_sup_left : K ≤ K ⊔ T) x.property⟩ = x

def groupInternalSummandFiltration : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (K T H : AddSubgroup G)
    (hH : H = K ⊔ T), Disjoint K T → ∀ (p : ℕ) (α : Ordinal.{v}) (x : K),
    ((⟨x, by rw [hH]; exact (le_sup_left : K ≤ K ⊔ T) x.property⟩ : H) ∈
      (transfiniteFiltration p α : AddSubgroup H) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup K))

end LogicLineages.ModelsAlgebra.PGroups.Targets
