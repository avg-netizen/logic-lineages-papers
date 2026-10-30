module
public import LogicLineages.OrdinalComparison.ExponentialRootGapTargets
public import LogicLineages.OrdinalComparison.TotientBoundProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualCubicExponentialEnvelope : Targets.ActualCubicExponentialEnvelope := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hsmall : r < 99
    · have hc : r = 96 ∨ r = 97 ∨ r = 98 := by omega
      rcases hc with rfl | rfl | rfl <;> decide
    · let t := r - 3
      have ht : 96 ≤ t := by dsimp [t]; omega
      have htr : t < r := by dsimp [t]; omega
      have hshift : r = t + 3 := by dsimp [t]; omega
      have hdiv : r / 3 = t / 3 + 1 := by omega
      have hi := ih t htr ht
      have hpoly : (t + 3) ^ 3 ≤ 2 * t ^ 3 := by
        have h2 := Nat.mul_le_mul_left t ht
        have h3 := Nat.mul_le_mul_left (t * t) ht
        nlinarith
      calc
        r ^ 3 = (t + 3) ^ 3 := by rw [hshift]
        _ ≤ 2 * t ^ 3 := hpoly
        _ < 2 * 2 ^ (t / 3) := Nat.mul_lt_mul_of_pos_left hi (by decide)
        _ = 2 ^ (r / 3) := by rw [hdiv, pow_succ]; omega

theorem actualDiscreteRootCountGap : Targets.ActualDiscreteRootCountGap := by
  intro r Delta s hr hDelta hs
  have hrpos : 0 < r := by omega
  have hpoly : (r + 1) * Delta < r ^ 3 := by
    have h1 : r + 1 ≤ r * r := by nlinarith
    have h2 := Nat.mul_le_mul_left r h1
    have h3 := Nat.mul_lt_mul_of_pos_left hDelta (Nat.succ_pos r)
    nlinarith
  have hfactor : (r + 1) * Delta < 2 ^ (r / 3) :=
    hpoly.trans (actualCubicExponentialEnvelope r hr)
  have hsadd : s + r / 3 ≤ r := by omega
  have hscaled : (r + 1) * (2 ^ s * Delta) < 2 ^ r := by
    calc
      (r + 1) * (2 ^ s * Delta) = 2 ^ s * ((r + 1) * Delta) := by ring
      _ < 2 ^ s * 2 ^ (r / 3) := Nat.mul_lt_mul_of_pos_left hfactor (Nat.two_pow_pos s)
      _ = 2 ^ (s + r / 3) := (pow_add _ _ _).symm
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hsadd
  exact Nat.lt_of_mul_lt_mul_left (hscaled.trans (actualFermatShapeTotientLowerBound r hrpos))

end LogicLineages.OrdinalComparison
