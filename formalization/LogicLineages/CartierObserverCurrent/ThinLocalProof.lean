module
public import LogicLineages.CartierObserverCurrent.ThinRationalProof

public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.Thin

theorem actualDifferentialCartierSquarePullout : Targets.ActualDifferentialCartierSquarePullout.{u} := by
  intro K _ _ _ f g
  have hf := actualRationalSquareRootDecomposition K f
  have he : g ^ 2 * f = (g * actualRationalSquareRootDigit false f) ^ 2 +
      RatFunc.X * (g * actualRationalSquareRootDigit true f) ^ 2 := by
    conv_lhs => rw [hf]
    ring
  rw [he, actualDifferentialCartierCharacterization]
  rfl

private theorem constant_sqrt_square {K : Type*} [Field K] [CharP K 2] [PerfectRing K 2]
    (b : K) : (RatFunc.C ((frobeniusEquiv K 2).symm b) : RatFunc K) ^ 2 = RatFunc.C b := by
  rw [← map_pow]
  exact congrArg RatFunc.C ((frobeniusEquiv K 2).apply_symm_apply b)

private theorem cartier_constant {K : Type*} [Field K] [CharP K 2] [PerfectRing K 2]
    (b : K) : actualDifferentialCartier (RatFunc.C b) = 0 := by
  have h := actualDifferentialCartierCharacterization K
    (RatFunc.C ((frobeniusEquiv K 2).symm b)) 0
  simpa only [constant_sqrt_square, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h

theorem actualDifferentialCartierLocalPowers : Targets.ActualDifferentialCartierLocalPowers.{u} := by
  intro K _ _ _ z b
  let h : RatFunc K := RatFunc.X - RatFunc.C z
  have hn : h ≠ 0 := by
    have h := RatFunc.algebraMap_ne_zero (K := K) (Polynomial.X_sub_C_ne_zero z)
    simpa [map_sub] using h
  have hc : actualDifferentialCartier h = 1 := by
    have h0 := actualDifferentialCartierCharacterization K
      (RatFunc.C ((frobeniusEquiv K 2).symm (-z))) 1
    rw [constant_sqrt_square] at h0
    simpa only [map_neg, one_pow, mul_one, neg_add_eq_sub] using h0
  refine ⟨hn, ?_⟩
  intro k
  have heven : (h ^ k) ^ 2 = h ^ (2 * k) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have he : RatFunc.C b * h ^ (2 * k) =
      (RatFunc.C ((frobeniusEquiv K 2).symm b) * h ^ k) ^ 2 := by
    rw [mul_pow, constant_sqrt_square, heven]
  have ho : RatFunc.C b * h ^ (2 * k + 1) =
      (RatFunc.C ((frobeniusEquiv K 2).symm b) * h ^ k) ^ 2 * h := by
    rw [mul_pow, constant_sqrt_square, heven, zpow_add₀ hn, zpow_one]
    ring
  constructor
  · change actualDifferentialCartier (RatFunc.C b * h ^ (2 * k)) = 0
    rw [he]
    have h0 := actualDifferentialCartierCharacterization K
      (RatFunc.C ((frobeniusEquiv K 2).symm b) * h ^ k) 0
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h0
  · change actualDifferentialCartier (RatFunc.C b * h ^ (2 * k + 1)) = _
    rw [ho, actualDifferentialCartierSquarePullout, hc, mul_one]

theorem evenSelectorIdentity : Targets.EvenSelectorIdentity.{u} := by
  intro K _ _ _ f
  have hf := actualRationalSquareRootDecomposition K f
  have he : RatFunc.X * f =
      (RatFunc.X * actualRationalSquareRootDigit true f) ^ 2 +
        RatFunc.X * (actualRationalSquareRootDigit false f) ^ 2 := by
    conv_lhs => rw [hf]
    ring
  rw [he, actualDifferentialCartierCharacterization]

theorem cartierAdd (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2]
    (f g : RatFunc K) :
    actualDifferentialCartier (f + g) =
      actualDifferentialCartier f + actualDifferentialCartier g := by
  have hf := actualRationalSquareRootDecomposition K f
  have hg := actualRationalSquareRootDecomposition K g
  have he : f + g =
      (actualRationalSquareRootDigit false f + actualRationalSquareRootDigit false g) ^ 2 +
      RatFunc.X * (actualRationalSquareRootDigit true f + actualRationalSquareRootDigit true g) ^ 2 := by
    rw [CharTwo.add_sq, CharTwo.add_sq]
    conv_lhs => rw [hf, hg]
    ring
  rw [he, actualDifferentialCartierCharacterization]
  rfl

theorem evenSelectorLocalPowers : Targets.EvenSelectorLocalPowers.{u} := by
  intro K _ _ _ z b k
  let h : RatFunc K := RatFunc.X - RatFunc.C z
  have hn : h ≠ 0 := (actualDifferentialCartierLocalPowers K z b).1
  have split (m : Int) : RatFunc.X * (RatFunc.C b * h ^ m) =
      RatFunc.C b * h ^ (m + 1) + RatFunc.C (z * b) * h ^ m := by
    rw [zpow_add₀ hn, zpow_one, map_mul]
    dsimp [h]
    ring
  have hb := (actualDifferentialCartierLocalPowers K z b).2
  have hzb := (actualDifferentialCartierLocalPowers K z (z * b)).2
  constructor
  · change actualDifferentialCartier (RatFunc.X * (RatFunc.C b * h ^ (2 * k))) = _
    rw [split, cartierAdd, (hb k).2, (hzb k).1, add_zero]
  · change actualDifferentialCartier (RatFunc.X * (RatFunc.C b * h ^ (2 * k + 1))) = _
    rw [split, cartierAdd]
    have hi : (2 * k + 1) + 1 = 2 * (k + 1) := by ring
    rw [hi, (hb (k + 1)).1, (hzb k).2, zero_add]

#audit_namespace LogicLineages.CartierObserverCurrent.Thin
end LogicLineages.CartierObserverCurrent.Thin
