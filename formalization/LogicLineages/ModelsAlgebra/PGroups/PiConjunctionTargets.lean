module

public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

/-- Same syntax can be promoted above a positive rank. Literal QF leaves
are honestly excluded and handled by explicit padding separately. -/
def groupPositiveComplexityMonotone : Prop :=
  ∀ (side : Polarity) (α β : Ordinal.{v}) (n : ℕ) (φ : Formula n),
    α ≠ 0 → α ≤ β → Complexity side α φ → Complexity side β φ

def groupPiOneNormalizationRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ : Formula n) (a : Fin n → G),
    (piOneNormalize φ).Realize a ↔ φ.Realize a

def groupPiOneNormalizationComplexity : Prop :=
  ∀ (γ : Ordinal.{v}), γ < 2 → ∀ (n : ℕ) (φ : Formula n),
    Complexity .pi γ φ → Complexity .pi (1 : Ordinal.{v}) (piOneNormalize φ)

def groupPiConjunctionRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ ψ : Formula n) (a : Fin n → G),
    (piConjunction φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a

/-- Actual branch flattening preserves every common positive Pi rank. -/
def groupPiConjunctionComplexity : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (n : ℕ) (φ ψ : Formula n),
    Complexity .pi α φ → Complexity .pi α ψ →
      Complexity .pi α (piConjunction φ ψ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
