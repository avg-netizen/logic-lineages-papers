module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v

def omegaBlockFiltration : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (δ : Ordinal.{v}),
    (transfiniteFiltration p (δ+Ordinal.omega0) : AddSubgroup G) =
      ⨅ n : ℕ, transfiniteFiltration p (δ+(n:Ordinal.{v}))

def finiteOmegaBlockBound : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p : ℕ) (D : AddSubgroup G) [Finite D]
    (δ : Ordinal.{v}), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      D ⊓ transfiniteFiltration p (δ+(n:Ordinal.{v})) =
        D ⊓ transfiniteFiltration p (δ+Ordinal.omega0)

end LogicLineages.ModelsAlgebra.PGroups.Targets
