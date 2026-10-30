module
public import LogicLineages.OrdinalComparison.TotientBoundTargets

@[expose] public section

/-! Source paper10 actual-period root-count argument, paper.tex580–591,621–631.
The exponent s of Frobenius is an actual natural number with 3s<=2r. The
floor-exponent envelope and resulting strict degree/primitive-root-count gap
are numerical theorems, not a claim about the printed real rpow inequality.
The eventual source application must supply r>=96 and Delta<r from Phi. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualCubicExponentialEnvelope : Prop :=
  ∀ r : Nat, 96 ≤ r → r ^ 3 < 2 ^ (r / 3)

def ActualDiscreteRootCountGap : Prop :=
  ∀ r Delta s : Nat, 96 ≤ r → Delta < r → 3 * s ≤ 2 * r →
    2 ^ s * Delta < Nat.totient (2 ^ r + 1)

end LogicLineages.OrdinalComparison.Targets
