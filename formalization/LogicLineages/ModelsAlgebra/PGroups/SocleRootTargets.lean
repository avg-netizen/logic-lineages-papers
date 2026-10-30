module

public import LogicLineages.ModelsAlgebra.PGroups.SocleRootDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

def groupSocleRootMatrix : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (p j n : ℕ)
    (a : Fin n → G) (x y : Fin 1 → G),
      (socleRootMatrix p j n).Realize (append (append a x) y) ↔
        (p • x 0 = 0 → p ^ j • y 0 = x 0)

def groupSocleRootWitnessFormula : Prop :=
  ∀ (p j n : ℕ), Complexity .sigma (1 : Ordinal.{v}) (socleRootWitnessFormula p j n) ∧
    ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G) (x : Fin 1 → G),
      (socleRootWitnessFormula p j n).Realize (append a x) ↔
        (p • x 0 = 0 → ∃ y : G, p ^ j • y = x 0)

/-- Actual original-language Pi_2 clause realizing socle containment in the
actual finite p-filtration. Holds for every natural p, hence source primes;
j=0 is included, with no absent-witness shortcut. -/
def groupSocleRootFormula : Prop :=
  ∀ (p j n : ℕ), Complexity .pi (2 : Ordinal.{v}) (socleRootFormula p j n) ∧
    ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (socleRootFormula p j n).Realize a ↔
        pSocle p (⊤ : AddSubgroup G) ≤ finiteFiltration p j

end LogicLineages.ModelsAlgebra.PGroups.Targets
