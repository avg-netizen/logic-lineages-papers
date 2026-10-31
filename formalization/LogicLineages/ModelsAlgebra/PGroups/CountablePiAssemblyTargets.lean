module
public import LogicLineages.ModelsAlgebra.PGroups.CountablePiAssemblyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def countablePiAssembly : Prop :=
  ∀ (α : Ordinal.{0}), α ≠ 0 → ∀ (ι : Type) [Countable ι] (n : ℕ) (φ : ι → Formula n),
    (∀ i, Complexity .pi α (φ i)) →
    ∃ ψ : Formula n, Complexity .pi α ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ ∀ i, (φ i).Realize a
end LogicLineages.ModelsAlgebra.PGroups.Targets
