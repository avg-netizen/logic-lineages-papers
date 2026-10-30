module
public import LogicLineages.OrdinalComparison.BinaryDenominatorDefinitions
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-! Actual source product suppliers for paper10 lem:residue, paper.tex550–565.
The field is an arbitrary extension of F2, the root is genuinely primitive,
and the modulus may be composite. The q=1 empty-product edge is included.
These statements do not yet assert any rational-differential residue. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualPrimitiveRootCompleteProduct : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ q : Nat, Odd q →
    ∀ z : K, IsPrimitiveRoot z q →
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator (q - 1)) = 1

def ActualPrimitiveRootPartialProductNonzero : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ q m : Nat, m < q →
    ∀ z : K, IsPrimitiveRoot z q →
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m) ≠ 0

end LogicLineages.OrdinalComparison.Targets
