module
public import LogicLineages.ModelsAlgebra.PGroups.ThreeRelativizationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u
def threeTransfiniteRelativization : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (side : Polarity)
    (n : ℕ) (φ : Formula n), Complexity side (3:Ordinal.{0}) φ →
    ∃ ψ : Formula n, Complexity side (2*γ+3) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a
end LogicLineages.ModelsAlgebra.PGroups.Targets
