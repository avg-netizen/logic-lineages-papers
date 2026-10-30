module
public import LogicLineages.OrdinalComparison.BinaryPoleBudgetDefinitions
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Literal uniform pole bound in source paper10 lem:poles. No primitive-root
or factorization premise replaces actual root multiplicity. -/
def ActualBinaryBinomialRootMultiplicity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2], ∀ n : Nat, 0 < n → ∀ z : K,
    (1 + Polynomial.X ^ n : Polynomial K).rootMultiplicity z ≤ 2 ^ padicValNat 2 n

def ActualBinarySourceRootMultiplicity : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (ZMod 2) K], ∀ d : Nat, ∀ z : K,
    ((actualBinarySourceDenominator d).map (algebraMap (ZMod 2) K)).rootMultiplicity z ≤
      actualBinaryPoleBudget d

end LogicLineages.OrdinalComparison.Targets
