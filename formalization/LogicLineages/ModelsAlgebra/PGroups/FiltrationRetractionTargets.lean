module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v w

def groupHomTransfiniteFiltration : Prop :=
  ∀ (G : Type u) (H : Type w) [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (p : ℕ) (α : Ordinal.{v}) (x : G),
    x ∈ (transfiniteFiltration p α : AddSubgroup G) →
    f x ∈ (transfiniteFiltration p α : AddSubgroup H)

def groupRetractionFiltrationReflection : Prop :=
  ∀ (G : Type u) (H : Type w) [AddCommGroup G] [AddCommGroup H]
    (i : G →+ H) (r : H →+ G), (∀ x, r (i x) = x) →
    ∀ (p : ℕ) (α : Ordinal.{v}) (x : G),
    (i x ∈ (transfiniteFiltration p α : AddSubgroup H) ↔
      x ∈ (transfiniteFiltration p α : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
