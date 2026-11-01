module
public import LogicLineages.ModelsAlgebra.PGroups.CloseAllDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def sigmaCloseAllCorrect : Prop :=
  ∀ (α:Ordinal.{0}), α≠0 → ∀ (n:ℕ) (φ:Formula n), Complexity .sigma α φ →
    Complexity .sigma α (sigmaCloseAll φ) ∧ ∀ (G:Type) [AddCommGroup G],
      (sigmaCloseAll φ).Realize (Fin.elim0:Fin 0→G) ↔ ∃a:Fin n→G,φ.Realize a
def piCloseAllCorrect : Prop :=
  ∀ (α:Ordinal.{0}), α≠0 → ∀ (n:ℕ) (φ:Formula n), Complexity .pi α φ →
    Complexity .pi α (piCloseAll φ) ∧ ∀ (G:Type) [AddCommGroup G],
      (piCloseAll φ).Realize (Fin.elim0:Fin 0→G) ↔ ∀a:Fin n→G,φ.Realize a
end LogicLineages.ModelsAlgebra.PGroups.Targets
