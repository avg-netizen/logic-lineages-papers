module
public import LogicLineages.CartierObserverCurrent.PoleContractionTargets
public import LogicLineages.CartierObserverCurrent.LocalPolynomialProof
public import Mathlib.Algebra.Polynomial.RingDivision
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PoleContraction

theorem actualRootFactorization : Targets.ActualRootFactorization.{u} := by
  intro K _ Q hQ z
  exact ⟨(Polynomial.pow_mul_divByMonic_rootMultiplicity_eq Q z).symm,
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hQ⟩

private theorem cartier_square_denominator (K : Type u) [Field K] [CharP K 2]
    [PerfectRing K 2] (P Q : Polynomial K) :
    Basic.actualDifferentialCartier
      (algebraMap (Polynomial K) (RatFunc K) P /
        (algebraMap (Polynomial K) (RatFunc K) Q) ^ 2) =
      algebraMap (Polynomial K) (RatFunc K) (Basic.actualPolynomialSquareRootDigit true P) /
        algebraMap (Polynomial K) (RatFunc K) Q := by
  let E := algebraMap (Polynomial K) (RatFunc K)
  have he : E P / (E Q) ^ 2 = ((E Q)⁻¹) ^ 2 * E P := by
    rw [div_eq_mul_inv, inv_pow]
    ring
  have hp := ((Basic.LocalPolynomial.localPolePolynomialRule K).2 P).1
  rw [he, Basic.actualDifferentialCartierSquarePullout, hp]
  ring

private theorem step_square_denominator_divides (K : Type u) [Field K] [CharP K 2]
    [PerfectRing K 2] (P Q : Polynomial K) (b : Bool) :
    (MixedProper.step b (algebraMap (Polynomial K) (RatFunc K) P /
      (algebraMap (Polynomial K) (RatFunc K) Q) ^ 2)).denom ∣ Q := by
  let E := algebraMap (Polynomial K) (RatFunc K)
  cases b
  · change (Basic.actualDifferentialCartier (Basic.rationalX * (E P / (E Q) ^ 2))).denom ∣ Q
    have he : Basic.rationalX * (E P / (E Q) ^ 2) = E (Polynomial.X * P) / (E Q) ^ 2 := by
      rw [map_mul]
      dsimp [E, Basic.rationalX]
      ring
    rw [he, cartier_square_denominator]
    exact RatFunc.denom_div_dvd _ _
  · change (Basic.actualDifferentialCartier (E P / (E Q) ^ 2)).denom ∣ Q
    rw [cartier_square_denominator]
    exact RatFunc.denom_div_dvd _ _

theorem fractionPoleContraction : Targets.FractionPoleContraction.{u} := by
  intro K _ _ _ P Q hQ b z
  let E := algebraMap (Polynomial K) (RatFunc K)
  let h : Polynomial K := Polynomial.X - Polynomial.C z
  let R := rootRemoved Q z
  let k := Q.rootMultiplicity z
  have hfac : Q = h ^ k * R := (actualRootFactorization K Q hQ z).1
  have hval : R.eval z ≠ 0 := (actualRootFactorization K Q hQ z).2
  have hR : R ≠ 0 := by intro hz; apply hval; rw [hz, Polynomial.eval_zero]
  have hh : h ≠ 0 := Polynomial.X_sub_C_ne_zero z
  have eh : E h ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have er : E R ≠ 0 := RatFunc.algebraMap_ne_zero hR
  have efac : E Q = (E h) ^ k * E R := by
    simpa only [map_mul, map_pow] using congrArg E hfac
  have bound (j : Nat) (N : Polynomial K)
      (he : E P / E Q = E N / (E (h ^ j * R)) ^ 2) :
      poleOrder z (MixedProper.step b (E P / E Q)) ≤ j := by
    have hd := step_square_denominator_divides K N (h ^ j * R) b
    rw [← he] at hd
    have hmult := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
      (mul_ne_zero (pow_ne_zero j hh) hR) hd z
    have hr : R.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero hval
    have hm : (h ^ j * R).rootMultiplicity z = j := by
      rw [mul_comm, Polynomial.rootMultiplicity_mul_X_sub_C_pow hR, hr, zero_add]
    exact hm ▸ hmult
  by_cases hk : 2 ∣ k
  · have hke : k = 2 * (k / 2) := by omega
    have he : E P / E Q = E (P * R) / (E (h ^ (k / 2) * R)) ^ 2 := by
      have hp : (E h) ^ k = ((E h) ^ (k / 2)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [efac, hp]
      simp only [map_mul, map_pow]
      field_simp
      <;> ring
    have hb := bound (k / 2) (P * R) he
    change poleOrder z (MixedProper.step b (E P / E Q)) ≤ (k + 1) / 2
    omega
  · have hko : k = 2 * (k / 2) + 1 := by omega
    have he : E P / E Q = E (h * P * R) / (E (h ^ (k / 2 + 1) * R)) ^ 2 := by
      have hp : (E h) ^ k = ((E h) ^ (k / 2)) ^ 2 * E h := by
        rw [← pow_mul, ← pow_succ]
        congr 1
        omega
      rw [efac, hp]
      simp only [map_mul, map_pow, pow_succ]
      field_simp
      <;> ring
    have hb := bound (k / 2 + 1) (h * P * R) he
    change poleOrder z (MixedProper.step b (E P / E Q)) ≤ (k + 1) / 2
    omega

theorem canonicalPoleContraction : Targets.CanonicalPoleContraction.{u} := by
  intro K _ _ _ f b z
  have h := fractionPoleContraction K f.num f.denom f.denom_ne_zero b z
  rw [RatFunc.num_div_denom] at h
  exact h

theorem noNewPole : Targets.NoNewPole.{u} := by
  intro K _ _ _ f b z hz
  have h := canonicalPoleContraction K f b z
  rw [hz] at h
  exact Nat.eq_zero_of_le_zero h

#audit_namespace LogicLineages.CartierObserverCurrent.PoleContraction
end LogicLineages.CartierObserverCurrent.PoleContraction
