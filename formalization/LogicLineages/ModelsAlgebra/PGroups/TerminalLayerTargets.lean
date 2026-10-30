module
public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupInternalSumQuotientImage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (K T H : AddSubgroup G),
    H = K ⊔ T → Disjoint K T →
    Nonempty (K ≃+ ↥(H.map (QuotientAddGroup.mk' T)))

def groupTerminalLayerQuotient : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T →
    Nonempty ((transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) ≃+ K)

end LogicLineages.ModelsAlgebra.PGroups.Targets
