module

public import LogicLineages.ModelsAlgebra.Differential.HyperplaneTargets
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.Hyperplane

open MvPolynomial

variable {K ι : Type*} [Field K] [DecidableEq ι]

private theorem difference_dvd (i : ι) (q : MvPolynomial ι K) :
    X i ∣ q - restrictZero i q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [restrictZero]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p j hp =>
    by_cases hji : j = i
    · subst j
      simpa [restrictZero] using (dvd_mul_left (X i : MvPolynomial ι K) p)
    · have he : restrictZero i (p * X j) = restrictZero i p * X j := by
        simp [restrictZero, hji]
      rw [he, ← sub_mul]
      exact dvd_mul_of_dvd_left hp _

theorem restriction_kernel : Targets.coordinateRestrictionKernel := by
  intro K ι _ _ i q
  constructor
  · rintro ⟨h, rfl⟩
    simp [restrictZero]
  · intro hq
    simpa only [hq, sub_zero] using difference_dvd i q

theorem product_missing_witness : Targets.coordinateProductMissingWitness := by
  intro K n _ q
  classical
  have hprod : (∏ i : Fin n, (X i : MvPolynomial (Fin n) K)) ∣ q ↔
      ∀ i : Fin n, (X i : MvPolynomial (Fin n) K) ∣ q := by
    constructor
    · intro h i
      exact (Finset.dvd_prod_of_mem (fun j : Fin n => (X j : MvPolynomial (Fin n) K))
        (Finset.mem_univ i)).trans h
    · intro h
      apply Fintype.prod_dvd_of_isRelPrime _ h
      intro i j hij
      apply (MvPolynomial.X_prime (i := i) : Prime (X i : MvPolynomial (Fin n) K)).irreducible.isRelPrime_iff_not_dvd.mpr
      simpa only [MvPolynomial.X_dvd_X] using hij
  rw [hprod]
  simp only [restriction_kernel K (Fin n), not_forall]

end LogicLineages.ModelsAlgebra.Differential.Hyperplane
