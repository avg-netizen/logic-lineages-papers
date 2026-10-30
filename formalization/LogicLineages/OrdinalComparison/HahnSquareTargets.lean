module
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Order.Ring.Int

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual Laurent coefficient algebra for the source Cartier local rule.
All integer exponents and arbitrary genuine Hahn series are retained. -/
def ActualHahnSquareEvenCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2], ∀ F : HahnSeries Int K, ∀ n : Int,
    (F ^ 2).coeff (2 * n) = (F.coeff n) ^ 2

def ActualHahnSquareOddCoefficient : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2], ∀ F : HahnSeries Int K, ∀ n : Int,
    (F ^ 2).coeff (2 * n + 1) = 0

end LogicLineages.OrdinalComparison.Targets
