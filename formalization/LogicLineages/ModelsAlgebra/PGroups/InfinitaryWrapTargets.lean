module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

def groupSigmaWrapRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ : Formula n) (a : Fin n → G),
    (sigmaWrap φ).Realize a ↔ φ.Realize a

def groupPiWrapRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ : Formula n) (a : Fin n → G),
    (piWrap φ).Realize a ↔ φ.Realize a

/-- Genuine opposite-polarity lift with a strictly smaller matrix rank. -/
def groupSigmaWrapComplexity : Prop :=
  ∀ (α β : Ordinal.{v}), α ≠ 0 → β < α → ∀ (n : ℕ) (φ : Formula n),
    Complexity .pi β φ → Complexity .sigma α (sigmaWrap φ)

def groupPiWrapComplexity : Prop :=
  ∀ (α β : Ordinal.{v}), α ≠ 0 → β < α → ∀ (n : ℕ) (φ : Formula n),
    Complexity .sigma β φ → Complexity .pi α (piWrap φ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
