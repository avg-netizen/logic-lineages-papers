module
public import LogicLineages.OrdinalComparison.CartierRationalTargets

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual rational local-rule suppliers, source paper10 lem:local. Integer
powers include both poles and polynomial terms. The formal Laurent-series
coefficient rule remains a separate calibration obligation. -/
def ActualDifferentialCartierSquarePullout : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ f g : RatFunc K,
    actualDifferentialCartier (g ^ 2 * f) = g * actualDifferentialCartier f

def ActualDifferentialCartierLocalPowers : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ z b : K,
    (RatFunc.X - RatFunc.C z : RatFunc K) ≠ 0 ∧
    ∀ k : Int,
      actualDifferentialCartier (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k)) = 0 ∧
      actualDifferentialCartier (RatFunc.C b * (RatFunc.X - RatFunc.C z) ^ (2 * k + 1)) =
        RatFunc.C ((frobeniusEquiv K 2).symm b) * (RatFunc.X - RatFunc.C z) ^ k

end LogicLineages.OrdinalComparison.Targets
