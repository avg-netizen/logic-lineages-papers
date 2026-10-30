module

public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

def groupAnnihilationFormula : Prop :=
  ∀ (c n : ℕ), Complexity .pi (1 : Ordinal.{v}) (annihilationFormula c n) ∧
    ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (annihilationFormula c n).Realize a ↔ ∀ x : G, c • x = 0

/-- The exact p^jG=0 source bound in terms of the actual finite filtration.
All p and j are covered; in particular j=0 means the actual trivial group. -/
def groupFiniteExponentFormula : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p j n : ℕ) (a : Fin n → G),
    (annihilationFormula (p ^ j) n).Realize a ↔
      (finiteFiltration p j : AddSubgroup G) = ⊥

end LogicLineages.ModelsAlgebra.PGroups.Targets
