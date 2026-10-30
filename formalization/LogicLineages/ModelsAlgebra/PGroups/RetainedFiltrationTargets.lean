module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupRetainedFiltrationReflection : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (A K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T →
    A ⊓ (transfiniteFiltration p δ : AddSubgroup G) ≤ K →
    ∀ (α : Ordinal.{v}) (x : G), x ∈ A ⊔ K →
    ((QuotientAddGroup.mk' T) x ∈ (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
