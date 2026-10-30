module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

def groupSigmaTwoAllRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (fs : List (Formula n)) (a : Fin n → G),
    (sigmaTwoAll fs).Realize a ↔ ∀ φ ∈ fs, φ.Realize a

def groupPiTwoAllRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (fs : List (Formula n)) (a : Fin n → G),
    (piTwoAll fs).Realize a ↔ ∀ φ ∈ fs, φ.Realize a

def groupDifferenceTwoAllRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (fs : List (DifferenceFormula n)) (a : Fin n → G),
    (differenceTwoAll fs).Realize a ↔ ∀ φ ∈ fs, φ.Realize a

def groupSigmaTwoAllComplexity : Prop :=
  ∀ (n : ℕ) (fs : List (Formula n)),
    (∀ φ ∈ fs, Complexity .sigma (2 : Ordinal.{v}) φ) →
      Complexity .sigma (2 : Ordinal.{v}) (sigmaTwoAll fs)

def groupPiTwoAllComplexity : Prop :=
  ∀ (n : ℕ) (fs : List (Formula n)),
    (∀ φ ∈ fs, Complexity .pi (2 : Ordinal.{v}) φ) →
      Complexity .pi (2 : Ordinal.{v}) (piTwoAll fs)

def groupDifferenceTwoAllComplexity : Prop :=
  ∀ (n : ℕ) (fs : List (DifferenceFormula n)),
    (∀ φ ∈ fs, φ.AtLevel (2 : Ordinal.{v})) →
      (differenceTwoAll fs).AtLevel (2 : Ordinal.{v})

def groupPositiveDifferenceComplexityMonotone : Prop :=
  ∀ (α β : Ordinal.{v}), α ≠ 0 → α ≤ β → ∀ (n : ℕ) (φ : DifferenceFormula n),
    φ.AtLevel α → φ.AtLevel β

end LogicLineages.ModelsAlgebra.PGroups.Targets
