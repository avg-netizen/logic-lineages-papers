module
public import LogicLineages.OrdinalComparison.PrimitiveRootProductTargets

@[expose] public section

/-! Source paper10 lem:residue complementary product (paper.tex560–565).
This is a literal source-polynomial identity at every primitive root of odd
order, including q=1,m=0. It is not a definition of a residue or a pole oracle. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualPrimitiveRootComplement : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ q m : Nat, Odd q → m < q →
    ∀ z : K, IsPrimitiveRoot z q →
      (Polynomial.eval₂ (algebraMap (ZMod 2) K) z
        (actualBinarySourceDenominator (q - 1 - m)))⁻¹ =
      (z ^ actualBinarySourceDimension m)⁻¹ *
        Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m)

end LogicLineages.OrdinalComparison.Targets
