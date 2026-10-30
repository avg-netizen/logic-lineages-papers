module

public import LogicLineages.ModelsAlgebra.Differential.OrderOneDivisionTargets
public import LogicLineages.ModelsAlgebra.Differential.OrderOne

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.OrderOneDivision

open Polynomial
universe u

/-- The root-set criterion can be tested by one ordinary polynomial division
in characteristic zero. This uses coefficient-extension reflection, not
an assumed effective factorization or an algorithm on chosen roots. -/
theorem radicalDerivativeDivisibility : Targets.radicalDerivativeDivisibility := by
  intro r q hr
  let e := algebraMap ℚ (AlgebraicClosure ℚ)
  have hrmap : r.map e ≠ 0 := Polynomial.map_ne_zero hr
  constructor
  · intro hrad
    apply (Polynomial.map_dvd_map' e).mp
    rw [Polynomial.map_mul, ← Polynomial.derivative_map]
    apply (Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul hrmap).mp
    intro c hc
    have hrc : aeval c r = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, e] using hc
    have hqc := Radical.radicalAmbientRootVanishing (AlgebraicClosure ℚ) r q c hr hrad hrc
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, e] using hqc
  · intro hdiv
    apply (Radical.rationalRadicalRootCriterion r q hr).mpr
    intro c hc
    have hm : r.map e ∣ (r.map e).derivative * q.map e := by
      simpa only [Polynomial.map_mul, Polynomial.derivative_map] using
        (Polynomial.map_dvd e hdiv)
    have hrc : (r.map e).IsRoot c := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, e] using hc
    have hqc := Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul hrmap hm hrc
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, e] using hqc

theorem orderOneDivisionCriterion : Targets.orderOneDivisionCriterion.{u} := by
  intro p q hp hdeg hq
  rw [OrderOne.orderOneCriterion p q hp hdeg hq]
  by_cases hr : p.eval 0 = 0
  · simp only [hr, ne_eq, not_true_eq_false, false_and]
  · rw [radicalDerivativeDivisibility (p.eval 0) q hr]

end LogicLineages.ModelsAlgebra.Differential.OrderOneDivision
