module

public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

def groupJoinLeftAssignment : Prop :=
  ∀ (G : Type u) (n m l : ℕ) (a : Fin n → G) (w : Fin (m + l) → G),
    (fun i => append a w (joinLeft n m l i)) =
      append a (fun i => w (Fin.castAdd l i))

def groupJoinRightAssignment : Prop :=
  ∀ (G : Type u) (n m l : ℕ) (a : Fin n → G) (w : Fin (m + l) → G),
    (fun i => append a w (joinRight n m l i)) =
      append a (fun i => w (Fin.natAdd m i))

/-- Truth is actual conjunction for all inputs, even outside the rank slice. -/
def groupSigmaTwoConjunctionRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ ψ : Formula n) (a : Fin n → G),
    (sigmaTwoConjunction φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a

/-- Only the source's Sigma_2 slice is claimed here, not arbitrary Sigma ranks. -/
def groupSigmaTwoConjunctionComplexity : Prop :=
  ∀ (n : ℕ) (φ ψ : Formula n),
    Complexity .sigma (2 : Ordinal.{v}) φ → Complexity .sigma (2 : Ordinal.{v}) ψ →
      Complexity .sigma (2 : Ordinal.{v}) (sigmaTwoConjunction φ ψ)

end LogicLineages.ModelsAlgebra.PGroups.Targets
