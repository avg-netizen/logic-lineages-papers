module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

def groupMultipleTermEvaluation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n c : ℕ) (t : GroupTerm n) (a : Fin n → G),
    (multipleTerm c t).eval a = c • t.eval a

def groupFiniteConjunctionRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n m : ℕ) (f : Fin m → QF n) (a : Fin n → G),
    (finiteAnd m f).Realize a ↔ ∀ i, (f i).Realize a

def groupDistinctMultipleMatrixRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (c n m : ℕ) (a : Fin n → G) (d : Fin m → G),
    (distinctMultipleMatrix c n m).Realize (append a d) ↔
      Function.Injective (fun i => c • d i)

/-- The Sigma_1 classification and exact actual witness semantics. Includes
c=0 and m=0; no positivity or existence promise is assumed. -/
def groupDistinctMultiplesFormula : Prop :=
  ∀ (c n m : ℕ), Complexity .sigma (1 : Ordinal.{v}) (distinctMultiples c n m) ∧
    ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
      (distinctMultiples c n m).Realize a ↔
        ∃ d : Fin m → G, Function.Injective (fun i => c • d i)

/-- The exact Pi_2 source upper-bound formula for infinitude of a multiple
image (in particular p^(k-1)G). This does not assert Scott categoricity. -/
def groupInfiniteMultipleImageFormula : Prop :=
  ∀ c : ℕ, Complexity .pi (2 : Ordinal.{v}) (infiniteMultipleImage c) ∧
    ∀ (G : Type u) [AddCommGroup G],
      (infiniteMultipleImage c).Realize (Fin.elim0 : Fin 0 → G) ↔
        Set.Infinite (Set.range (fun x : G => c • x))

end LogicLineages.ModelsAlgebra.PGroups.Targets
