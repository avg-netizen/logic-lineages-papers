module
public import LogicLineages.OrdinalComparison.PrimitiveRootProductTargets
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-! Exact simple-root suppliers in paper10 lem:residue (paper.tex550–559).
The actual complete source polynomial and its literal formal derivative are
evaluated through the F2 coefficient embedding. No root or pole condition
replaces either conclusion; only the stated primitive-root/source-range
hypotheses are used. Differential residue semantics remain separate. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualPrimitiveRootSourceDerivative : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ q d : Nat,
    Odd q → q ≤ d → d < 2 * q → ∀ z : K, IsPrimitiveRoot z q →
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator d) = 0 ∧
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator d).derivative =
        z⁻¹ * Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator (d - q))

def ActualPrimitiveRootSourceDerivativeNonzero : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ q d : Nat,
    Odd q → q ≤ d → d < 2 * q → ∀ z : K, IsPrimitiveRoot z q →
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator d).derivative ≠ 0

end LogicLineages.OrdinalComparison.Targets
