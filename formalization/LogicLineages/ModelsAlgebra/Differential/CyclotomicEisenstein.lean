module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicGeometric
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.Maximal

@[expose] public section

/-! The paper's direct Eisenstein proof at ell, using its literal geometric
polynomial. This avoids importing the general cyclotomic construction's
Complex/Moebius closure; no irreducibility supplier is assumed. -/
namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

open Polynomial

private theorem shift_coeff (ℓ k : ℕ) :
    ((geometric ℤ ℓ).comp (X + 1)).coeff k = (ℓ.choose (k + 1) : ℤ) := by
  have h := congrArg (fun p : Polynomial ℤ => p.comp (X + 1)) (geometric_mul ℤ ℓ)
  have hshift : (geometric ℤ ℓ).comp (X + 1) * X = (X + 1) ^ ℓ - 1 := by
    simpa only [mul_comp, sub_comp, pow_comp, X_comp, one_comp, add_sub_cancel_right] using h
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff (k + 1)) hshift
  rw [coeff_mul_X, coeff_sub, coeff_X_add_one_pow] at hc
  have hone : (1 : Polynomial ℤ).coeff (k + 1) = 0 := by
    rw [← C_1, coeff_C]
    simp
  simpa only [hone, sub_zero] using hc

theorem prime_irreducible : Targets.cyclotomicPrimeIrreducible := by
  intro ℓ hp
  let q : Polynomial ℤ := (geometric ℤ ℓ).comp (X + 1)
  have hgeom := geometric_coefficients ℤ ℓ hp.pos
  have hqm : q.Monic := by
    simpa only [q, C_1] using hgeom.2.1.comp_X_add_C (1 : ℤ)
  have hqd : q.natDegree = ℓ - 1 := by
    have hlin : (X + (1 : Polynomial ℤ)).natDegree = 1 := by
      simpa only [C_1] using natDegree_X_add_C (1 : ℤ)
    change ((geometric ℤ ℓ).comp (X + 1)).natDegree = ℓ - 1
    rw [natDegree_comp, hgeom.2.2, hlin, mul_one]
  have hq0 : q.coeff 0 = (ℓ : ℤ) := by
    change ((geometric ℤ ℓ).comp (X + 1)).coeff 0 = (ℓ : ℤ)
    rw [shift_coeff]
    simp
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hp
  let P : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hlead : q.leadingCoeff ∉ P := by
    rw [hqm.leadingCoeff]
    exact hprime.not_dvd_one ∘ Ideal.mem_span_singleton.mp
  have hcoeff : ∀ k : ℕ, (k : WithBot ℕ) < q.degree → q.coeff k ∈ P := by
    intro k hk
    have hk' : k < ℓ - 1 := by
      have ht := Polynomial.coe_lt_degree.mp hk
      rwa [hqd] at ht
    apply Ideal.mem_span_singleton.mpr
    change (ℓ : ℤ) ∣ ((geometric ℤ ℓ).comp (X + 1)).coeff k
    rw [shift_coeff]
    exact_mod_cast hp.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
  have hdegree : 0 < q.degree := by
    rw [degree_eq_natDegree hqm.ne_zero, hqd]
    have ht := hp.two_le
    exact_mod_cast (show 0 < ℓ - 1 by omega)
  have hconstant : q.coeff 0 ∉ P ^ 2 := by
    intro hin
    rw [hq0] at hin
    change (ℓ : ℤ) ∈ (Ideal.span {(ℓ : ℤ)}) ^ 2 at hin
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hin
    have hdiv : (ℓ : ℤ) * (ℓ : ℤ) ∣ (ℓ : ℤ) * 1 := by
      simpa only [pow_two, mul_one] using hin
    exact hprime.not_dvd_one ((mul_dvd_mul_iff_left hprime.ne_zero).mp hdiv)
  have hiq : Irreducible q :=
    irreducible_of_eisenstein_criterion hP hlead hcoeff hdegree hconstant hqm.isPrimitive
  have hi : Irreducible (geometric ℤ ℓ) := by
    apply (MulEquiv.irreducible_iff (Polynomial.taylorEquiv (1 : ℤ))).mp
    have ht := LinearMap.congr_fun (coe_taylorEquiv (r := (1 : ℤ))) (geometric ℤ ℓ)
    simp only [LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv] at ht
    rw [ht, taylor_apply]
    simpa only [q, C_1] using hiq
  change Irreducible (geometric ℚ ℓ)
  rw [← geometric_map (Int.castRingHom ℚ) ℓ]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    hgeom.2.1.isPrimitive).mp hi

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
