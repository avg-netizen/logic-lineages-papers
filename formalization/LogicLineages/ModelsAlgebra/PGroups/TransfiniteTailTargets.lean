module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupTransfiniteTailMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ β : Ordinal.{v})
    (x : (transfiniteFiltration p δ : AddSubgroup G)),
    (x ∈ (transfiniteFiltration p β : AddSubgroup (transfiniteFiltration p δ : AddSubgroup G)) ↔
      (x : G) ∈ (transfiniteFiltration p (δ+β) : AddSubgroup G))

def groupTransfiniteTailImage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ β : Ordinal.{v}),
    (transfiniteFiltration p β : AddSubgroup (transfiniteFiltration p δ : AddSubgroup G)).map
      (transfiniteFiltration p δ : AddSubgroup G).subtype =
      (transfiniteFiltration p (δ+β) : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
