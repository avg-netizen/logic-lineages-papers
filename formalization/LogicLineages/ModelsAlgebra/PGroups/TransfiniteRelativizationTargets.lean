module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteRelativizationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth GroupInfinitary
universe u

def relativizedDualRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (S : AddSubgroup G) (n : ℕ) (φ : Formula n) (a : Fin n → G),
    φ.dual.RealizeIn S a ↔ ¬ φ.RealizeIn S a

def blockMembershipGuard : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (n m : ℕ),
    ∃ φ : Formula (n+m), Complexity .pi (2*γ) φ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin (n+m) → G),
        φ.Realize a ↔ ∀ i : Fin m,
          a (Fin.natAdd n i) ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G)

def lowTransfiniteRelativization : Prop :=
  ∀ (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType] (side : Polarity)
    (r : ℕ), r=1 ∨ r=2 → ∀ (n : ℕ) (φ : Formula n),
    Complexity side (r:Ordinal.{0}) φ →
    ∃ ψ : Formula n, Complexity side (2*γ+r) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a
end LogicLineages.ModelsAlgebra.PGroups.Targets
