module
public import LogicLineages.OrdinalComparison.BinaryPoleBudgetDefinitions
public import LogicLineages.OrdinalComparison.CartierProperDefinitions
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions
public import Mathlib.Data.Nat.Log

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

noncomputable def actualBinaryPoleTransient (d : Nat) : Nat := Nat.clog 2 (actualBinaryPoleBudget d)

/-- Actual rational differential with literal mapped source denominator A_d. -/
noncomputable def actualBinaryRationalDifferential {K : Type u} [Field K] [Algebra (ZMod 2) K]
    (d : Nat) (U : Polynomial K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) U /
    algebraMap (Polynomial K) (RatFunc K)
      ((actualBinarySourceDenominator d).map (algebraMap (ZMod 2) K))

end LogicLineages.OrdinalComparison
