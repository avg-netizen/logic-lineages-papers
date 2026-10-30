module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupHigherPerturbationProper : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B : AddSubgroup G) (x v : G) (α : Ordinal.{v}),
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) →
    (∀ (b : B) (β : Ordinal.{v}), x+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    v ∈ (transfiniteFiltration p (α+1) : AddSubgroup G) →
    x+v ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
    x+v ∉ (transfiniteFiltration p (α+1) : AddSubgroup G) ∧ x+v ∉ B ∧
    ∀ (b : B) (β : Ordinal.{v}), (x+v)+b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x+v ∈ (transfiniteFiltration p β : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
