module

public import LogicLineages.ModelsAlgebra.Differential.CyclotomicEisenstein
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily

open Polynomial

theorem prime_spectral_promise : Targets.cyclotomicPrimeSpectralPromise := by
  intro ℓ hp
  let f := polynomial ℓ
  let K := f.SplittingField
  have hg := geometric_coefficients ℚ ℓ hp.pos
  have hm : f.Monic := hg.2.1
  have hd : f.natDegree = ℓ - 1 := hg.2.2
  have hn : 0 < f.natDegree := by
    rw [hd]
    have ht := hp.two_le
    omega
  have hmapd : (f.map (algebraMap ℚ K)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    rw [natDegree_map]
    exact Nat.ne_of_gt hn
  obtain ⟨ζ, hζ⟩ := (SplittingField.splits f).exists_eval_eq_zero hmapd
  have hζgeom : (geometric K ℓ).eval ζ = 0 := by
    change ((geometric ℚ ℓ).map (algebraMap ℚ K)).eval ζ = 0 at hζ
    rw [geometric_map] at hζ
    exact hζ
  have hζzero : ζ ≠ 0 := by
    intro heq
    have hbad : (1 : K) = 0 := by
      have h := hζgeom
      rw [heq, ← coeff_zero_eq_eval_zero, geometric_coeff, if_pos hp.pos] at h
      exact h
    exact one_ne_zero hbad
  have hζone : ζ ≠ 1 := by
    intro heq
    have hbad : (ℓ : K) = 0 := by
      simpa [heq, geometric] using hζgeom
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) hbad
  have hζpow : ζ ^ ℓ = 1 := by
    have h := congrArg (fun p : Polynomial K => p.eval ζ) (geometric_mul K ℓ)
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, hζgeom, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have horder : orderOf ζ = ℓ := by
    rcases hp.eq_one_or_self_of_dvd (orderOf ζ) (orderOf_dvd_of_pow_eq_one hζpow) with h | h
    · exact False.elim (hζone (orderOf_eq_one_iff.mp h))
    · exact h
  have hmin : f = minpoly ℚ ζ := by
    apply minpoly.eq_of_irreducible_of_monic (prime_irreducible ℓ hp) _ hm
    change Polynomial.aeval ζ f = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hζ
  let root : Fin f.natDegree → K := fun i => ζ ^ (i.val + 1)
  have hbase : LinearIndependent ℚ (fun i : Fin f.natDegree => ζ ^ i.val) := by
    have h := linearIndependent_pow (K := ℚ) ζ
    rwa [← hmin] at h
  have hker : LinearMap.ker (LinearMap.mulLeft ℚ ζ) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun _ _ h => mul_left_cancel₀ hζzero h)
  have hLI : LinearIndependent ℚ root := by
    simpa only [root, Function.comp_def, LinearMap.mulLeft_apply, ← pow_succ'] using
      hbase.map' (LinearMap.mulLeft ℚ ζ) hker
  have hroot (i : Fin f.natDegree) : (f.map (algebraMap ℚ K)).IsRoot (root i) := by
    have hi : i.val + 1 < ℓ := by
      have ht := i.isLt
      omega
    have hne : root i ≠ 1 :=
      pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero i.val) (by rwa [horder])
    have hpow : root i ^ ℓ = 1 := by
      change (ζ ^ (i.val + 1)) ^ ℓ = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζpow, one_pow]
    have h := congrArg (fun p : Polynomial K => p.eval (root i)) (geometric_mul K ℓ)
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, hpow, sub_self] at h
    have heval : (geometric K ℓ).eval (root i) = 0 :=
      (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
    change (f.map (algebraMap ℚ K)).eval (root i) = 0
    change ((geometric ℚ ℓ).map (algebraMap ℚ K)).eval (root i) = 0
    rw [geometric_map]
    exact heval
  have hprodMonic : (∏ i : Fin f.natDegree, (X - C (root i))).Monic :=
    monic_prod_of_monic Finset.univ (fun i => X - C (root i)) (fun i _ => monic_X_sub_C (root i))
  have hprodDegree : (∏ i : Fin f.natDegree, (X - C (root i))).natDegree = f.natDegree := by
    rw [natDegree_prod_of_monic Finset.univ (fun i => X - C (root i))
      (fun i _ => monic_X_sub_C (root i))]
    simp
  have hprodDvd : (∏ i : Fin f.natDegree, (X - C (root i))) ∣ f.map (algebraMap ℚ K) :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hLI.injective)
      (fun i => dvd_iff_isRoot.mpr (hroot i))
  have hfactor : f.map (algebraMap ℚ K) = ∏ i : Fin f.natDegree, (X - C (root i)) :=
    eq_of_monic_of_dvd_of_natDegree_le hprodMonic (hm.map (algebraMap ℚ K)) hprodDvd
      (by rw [natDegree_map, hprodDegree])
  exact ⟨hm, hd, hn, root, hLI, hfactor⟩

theorem orders_unbounded : Targets.cyclotomicOrdersUnbounded := by
  intro N
  obtain ⟨ℓ, hbound, hp⟩ := Nat.exists_infinite_primes (N + 2)
  refine ⟨ℓ, hp, ?_⟩
  have hd := (geometric_coefficients ℚ ℓ hp.pos).2.2
  change N < (geometric ℚ ℓ).natDegree
  rw [hd]
  omega

end LogicLineages.ModelsAlgebra.Differential.CyclotomicFamily
