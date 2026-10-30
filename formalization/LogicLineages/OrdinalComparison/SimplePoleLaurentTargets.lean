module
public import LogicLineages.OrdinalComparison.SimplePoleLaurentDefinitions

@[expose] public section

/-! Genuine local Laurent-series semantics for the simple-pole residue used
in source paper10 lem:residue. Residue is not defined as U(z)/A'(z): that
formula, denominator reconstruction, and absence of lower powers are proved
about an actual HahnSeries Int K in the translated coordinate t=X-z. -/

universe u

namespace LogicLineages.OrdinalComparison.Targets

def ActualSimplePoleExpansionReconstruction : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, ∀ z : K,
    A.eval z = 0 → A.derivative.eval z ≠ 0 →
      HahnSeries.ofPowerSeries Int K (actualShiftedPolynomial A z : PowerSeries K) *
        actualSimplePoleExpansion A U z =
      HahnSeries.ofPowerSeries Int K (actualShiftedPolynomial U z : PowerSeries K)

def ActualSimplePoleExpansionResidue : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, ∀ z : K,
    A.eval z = 0 → A.derivative.eval z ≠ 0 →
      (actualSimplePoleExpansion A U z).coeff (-1) = U.eval z / A.derivative.eval z

def ActualSimplePoleExpansionLowerSupport : Prop :=
  ∀ (K : Type u) [Field K], ∀ A U : Polynomial K, ∀ z : K,
    A.eval z = 0 → A.derivative.eval z ≠ 0 → ∀ n : Int, n < -1 →
      (actualSimplePoleExpansion A U z).coeff n = 0

end LogicLineages.OrdinalComparison.Targets
