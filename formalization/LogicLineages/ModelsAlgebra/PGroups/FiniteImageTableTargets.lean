module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v w

def groupTableTermEvaluation : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K]
    (G : Type u) [AddCommGroup G] (c n : ℕ) (a : Fin n → G)
    (d : Fin (Fintype.card K) → G) (x : K),
      (tableTerm K c n x).eval (append a d) = c • d (Fintype.equivFin K x)

def groupFiniteImageTableMatrix : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K]
    (G : Type u) [AddCommGroup G] (c n : ℕ) (a : Fin n → G)
    (d : Fin (Fintype.card K) → G),
      let value : K → G := fun x => c • d (Fintype.equivFin K x)
      (finiteImageTableMatrix K c n).Realize (append a d) ↔
        Function.Injective value ∧ value 0 = 0 ∧
          (∀ x : K, value (-x) = -value x) ∧
            ∀ x y : K, value (x + y) = value x + value y

/-- Literal Sigma_1 table formula iff an actual injective additive hom into
the actual multiple-image subgroup. No table/embedding supplier is assumed. -/
def groupFiniteImageTableFormula : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K] (c n : ℕ),
    Complexity .sigma (1 : Ordinal.{v}) (finiteImageTableFormula K c n) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (finiteImageTableFormula K c n).Realize a ↔
          ∃ f : K →+ multipleImage G c, Function.Injective f

/-- Entire finite-image definability paragraph: the actual image is
additively isomorphic to the designated finite group. This does not give the
remaining Ulm-invariant descriptions or the full Scott classification. -/
def groupFiniteImageIsomorphismFormula : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K] (c : ℕ),
    (finiteImageIsomorphismFormula K c).AtLevel (1 : Ordinal.{v}) ∧
      ∀ (G : Type u) [AddCommGroup G],
        (finiteImageIsomorphismFormula K c).Realize (Fin.elim0 : Fin 0 → G) ↔
          Nonempty (multipleImage G c ≃+ K)

end LogicLineages.ModelsAlgebra.PGroups.Targets
