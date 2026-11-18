module
public import LogicLineages.CartierObserverCurrent.LocalPolynomialTargets
public import LogicLineages.CartierObserverCurrent.BasicLocalProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Basic.LocalPolynomial

theorem localPolePolynomialRule : Targets.LocalPolePolynomialRule.{u} := by
  intro K _ _ _
  constructor
  · intro z b j
    have h := (actualDifferentialCartierLocalPowers K z b).2
    have he : (2 : Int) * -(j : Int) = -((2 * j : Nat) : Int) := by omega
    have ho : (2 : Int) * -((j + 1 : Nat) : Int) + 1 =
        -((2 * j + 1 : Nat) : Int) := by omega
    constructor
    · simpa only [he, zpow_neg, zpow_natCast, div_eq_mul_inv] using (h (-(j : Int))).1
    · simpa only [ho, zpow_neg, zpow_natCast, div_eq_mul_inv] using
        (h (-((j + 1 : Nat) : Int))).2
  · intro P
    constructor
    · have he := congrArg (algebraMap (Polynomial K) (RatFunc K))
        (actualPolynomialSquareRootDecomposition K P)
      simp only [map_add, map_mul, map_pow] at he
      rw [he]
      exact actualDifferentialCartierCharacterization K _ _
    · intro n
      rw [actualPolynomialSquareRootDigit, Polynomial.coeff_map,
        actualBinaryPolynomialDigitCoefficient]
      rfl

#audit_namespace LogicLineages.CartierObserverCurrent.Basic.LocalPolynomial
end LogicLineages.CartierObserverCurrent.Basic.LocalPolynomial
