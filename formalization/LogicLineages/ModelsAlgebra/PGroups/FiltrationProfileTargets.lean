module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupFiltrationProfileTotal : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (x y : G),
    (∀ α : Ordinal.{v}, x ∈ (transfiniteFiltration p α : AddSubgroup G) →
      y ∈ (transfiniteFiltration p α : AddSubgroup G)) ∨
    (∀ α : Ordinal.{v}, y ∈ (transfiniteFiltration p α : AddSubgroup G) →
      x ∈ (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
