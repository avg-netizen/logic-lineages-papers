module
public import LogicLineages.OrdinalComparison.RangeAffineProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- A nonempty actual source kernel word on an open P argument dominates
Phi(x), not merely x, on its computed genuine-domain tail. -/
def ActualSourceRangePhiLowerBound : Prop :=
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range w E) → ∀ x : Nat,
    oneVariableComparisonDomainBound (.range w E)≤x →
    Phi x≤actualOneVariableComparisonValue (.range w E) x

/-- Complete terminating R/affine P rule, with genuine uniform primitive
recursive numeric tail and literal source values/domains. -/
def ActualSourceRangeAffineProgram : Prop :=
  Primrec (fun p : Nat × Nat × Nat => encodedRangeAffineTail p.1 p.2.1 p.2.2) ∧
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range w E) → ∀ a b : Nat,
    1≤encodedRangeAffineTail (oneVariableComparisonEncode (.range w E)) a b ∧
    ∀ x : Nat, encodedRangeAffineTail (oneVariableComparisonEncode (.range w E)) a b≤x →
      oneVariableComparisonDomainAt (.range w E) x ∧
      a*x+b<actualOneVariableComparisonValue (.range w E) x

end LogicLineages.OrdinalComparison.Targets
