module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneTargets

@[expose] public section

/-! A direct characteristic-zero divisibility test, equivalent to the source
radical criterion. This mathematical bridge precedes its proof. It avoids a
separate factorization/gcd algorithm; actual encoded division is still needed
before the effective source corollary is complete. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

universe u

def radicalDerivativeDivisibility : Prop :=
  ∀ r q : Polynomial ℚ, r ≠ 0 →
    (rationalRadical r ∣ q ↔ r ∣ r.derivative * q)

def orderOneDivisionCriterion : Prop :=
  ∀ (p : BivariatePolynomial) (q : Polynomial ℚ),
    Irreducible p → 0 < p.natDegree → q ≠ 0 →
    (ConstrainedOrderOne.{u} p q ↔
      p.eval 0 ≠ 0 ∧ p.eval 0 ∣ (p.eval 0).derivative * q)

end LogicLineages.ModelsAlgebra.Differential.Targets
