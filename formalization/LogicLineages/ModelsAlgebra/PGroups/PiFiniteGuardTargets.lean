module
public import LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u

def piFiniteGuardExact : Prop :=
  ∀ (α : Ordinal.{0}) (n : ℕ) (fs : List (Formula n)),
    (∀ φ ∈ fs, Complexity .pi α φ) →
    Complexity .pi α (piFiniteGuard α fs) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (piFiniteGuard α fs).Realize a ↔ ∀ φ ∈ fs, φ.Realize a

def piSuccessorPadding : Prop :=
  ∀ (α : Ordinal.{0}) (n : ℕ) (φ : Formula n), Complexity .pi α φ →
    Complexity .pi (α+1) (piOneNormalize φ) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (piOneNormalize φ).Realize a ↔ φ.Realize a
end LogicLineages.ModelsAlgebra.PGroups.Targets
