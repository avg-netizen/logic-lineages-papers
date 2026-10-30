module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def groupExactHeightBelowCut : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}) (x : G),
    x ∉ (transfiniteFiltration p δ : AddSubgroup G) →
    ∃ α : Ordinal.{v}, α < δ ∧ x ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
      x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G)

def groupExactHeightZeroStage : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}),
    (transfiniteFiltration p δ : AddSubgroup G) = ⊥ → ∀ x : G, x ≠ 0 →
    ∃ α : Ordinal.{v}, α < δ ∧ x ∈ (transfiniteFiltration p α : AddSubgroup G) ∧
      x ∉ (transfiniteFiltration p (α+1) : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
