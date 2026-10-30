module
public import LogicLineages.OrdinalComparison.RealResidueBoundsTargets
public import LogicLineages.OrdinalComparison.LinkedResidueProof
public import LogicLineages.OrdinalComparison.ExponentialRootGapProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualRealExponentialRootGap : Targets.ActualRealExponentialRootGap := by
  intro r Delta hr hDelta
  have hpoly : (r + 1) * Delta < r ^ 3 := by
    have h1 : r + 1 ≤ r * r := by nlinarith
    have h2 := Nat.mul_le_mul_left r h1
    have h3 := Nat.mul_lt_mul_of_pos_left hDelta (Nat.succ_pos r)
    nlinarith
  have hfloor : ((r / 3 : Nat) : Real) ≤ (r : Real) / 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 3)).mpr
    exact_mod_cast Nat.div_mul_le_self r 3
  have hpow : (2 : Real) ^ (r / 3) ≤ Real.rpow 2 ((r : Real) / 3) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  have hbound : ((r : Real) + 1) * (Delta : Real) < Real.rpow 2 ((r : Real) / 3) := by
    calc
      ((r : Real) + 1) * (Delta : Real) < (r : Real) ^ 3 := by exact_mod_cast hpoly
      _ < (2 : Real) ^ (r / 3) := by exact_mod_cast actualCubicExponentialEnvelope r hr
      _ ≤ Real.rpow 2 ((r : Real) / 3) := hpow
  have hscaled := mul_lt_mul_of_pos_left hbound
    (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) (2 * (r : Real) / 3))
  change (2 : Real) ^ (2 * (r : Real) / 3) * (((r : Real) + 1) * (Delta : Real)) <
    (2 : Real) ^ (2 * (r : Real) / 3) * (2 : Real) ^ ((r : Real) / 3) at hscaled
  rw [← Real.rpow_add (by norm_num : (0 : Real) < 2),
    show 2 * (r : Real) / 3 + (r : Real) / 3 = (r : Real) by ring,
    Real.rpow_natCast] at hscaled
  change (2 : Real) ^ (2 * (r : Real) / 3) * (Delta : Real) < (2 : Real) ^ r / ((r : Real) + 1)
  apply (lt_div_iff₀ (by positivity : (0 : Real) < (r : Real) + 1)).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled

theorem fullActualLinkedResidueBounds : Targets.FullActualLinkedResidueBounds := by
  intro u hu
  obtain ⟨hr, hD, _h2e, hpos, hupper, _rest⟩ := actualLinkedResidueArithmetic u hu
  refine ⟨hr, hD, hpos, hupper, ?_, actualRealExponentialRootGap _ _ hr hD⟩
  apply (div_lt_iff₀ (by positivity : (0 : Real) < (actualLinkedHalfExponent u : Real) + 1)).mpr
  have hnat := actualFermatShapeTotientLowerBound (actualLinkedHalfExponent u) (by omega)
  have hcast : (2 : Real) ^ actualLinkedHalfExponent u <
      ((actualLinkedHalfExponent u : Real) + 1) *
        (Nat.totient (2 ^ actualLinkedHalfExponent u + 1) : Real) := by
    exact_mod_cast hnat
  simpa only [actualLinkedModulus, mul_comm] using hcast

end LogicLineages.OrdinalComparison
