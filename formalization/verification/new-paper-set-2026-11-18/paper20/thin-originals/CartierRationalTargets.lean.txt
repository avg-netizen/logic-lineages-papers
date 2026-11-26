module
public import LogicLineages.OrdinalComparison.CartierRationalDefinitions
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Exact source definition of differential Cartier, paper10 lines460–466:
existence and uniqueness are paid on real RatFunc, including f=0. -/
def ActualRationalSquareRootDecomposition : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f : RatFunc K,
    f = (actualRationalSquareRootDigit false f) ^ 2 +
      RatFunc.X * (actualRationalSquareRootDigit true f) ^ 2

def ActualRationalSquareRootUniqueness : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b c d : RatFunc K,
    a ^ 2 + RatFunc.X * b ^ 2 = c ^ 2 + RatFunc.X * d ^ 2 → a = c ∧ b = d

def ActualDifferentialCartierCharacterization : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ a b : RatFunc K,
    actualDifferentialCartier (a ^ 2 + RatFunc.X * b ^ 2) = b

end LogicLineages.OrdinalComparison.Targets
