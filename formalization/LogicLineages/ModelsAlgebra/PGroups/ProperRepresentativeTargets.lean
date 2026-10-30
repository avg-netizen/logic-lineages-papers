module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupProperRepresentative : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (B : AddSubgroup G) (x : G) (α : Ordinal.{v}),
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x ∉ (transfiniteFiltration p (α + 1) : AddSubgroup G) →
    (∀ b : B, ∀ β : Ordinal.{v},
      x + b ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G)) →
    ∀ b : B, x + b ∈ (transfiniteFiltration p α : AddSubgroup G) →
      ∀ c : B, ∀ β : Ordinal.{v},
        x + c ∈ (transfiniteFiltration p β : AddSubgroup G) →
        x + b ∈ (transfiniteFiltration p β : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
