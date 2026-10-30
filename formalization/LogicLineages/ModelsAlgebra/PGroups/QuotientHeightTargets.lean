module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupQuotientMembershipReflection : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (T : AddSubgroup G) (δ : Ordinal.{v}),
    T ≤ transfiniteFiltration p δ → ∀ (α : Ordinal.{v}), α ≤ δ → ∀ x : G,
    ((QuotientAddGroup.mk' T) x ∈ (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup G))

def groupQuotientSuccessorHeightReflection : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (T : AddSubgroup G) (δ : Ordinal.{v}),
    T ≤ transfiniteFiltration p δ → ∀ (α : Ordinal.{v}), α + 1 ≤ δ → ∀ x : G,
    ((QuotientAddGroup.mk' T) x ∈ (transfiniteFiltration p α : AddSubgroup (G ⧸ T)) ∧
      (QuotientAddGroup.mk' T) x ∉ (transfiniteFiltration p (α+1) : AddSubgroup (G ⧸ T))) ↔
    (x ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
      x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
