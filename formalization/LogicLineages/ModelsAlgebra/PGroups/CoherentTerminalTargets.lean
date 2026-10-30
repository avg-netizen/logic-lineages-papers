module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupCoherentTerminalQuotient : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T →
    ∃ e : K ≃+ (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)),
      ∀ x : K, (e x : G ⧸ T) = (QuotientAddGroup.mk' T) (x : G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
