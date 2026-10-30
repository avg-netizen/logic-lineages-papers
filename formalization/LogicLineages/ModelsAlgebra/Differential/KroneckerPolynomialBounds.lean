module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial

variable {K : Type*} [CommRing K]

private theorem box_iff_degreeOf {n B : ℕ} (p : MvPolynomial (Fin n) K) (hB : 0 < B) :
    Box B p ↔ ∀ i : Fin n, p.degreeOf i < B := by
  constructor
  · intro hp i
    exact (MvPolynomial.degreeOf_lt_iff hB).mpr (fun d hd => hp d hd i)
  · intro hp d hd i
    exact (MvPolynomial.degreeOf_lt_iff hB).mp (hp i) d hd

theorem box_exists : Targets.kroneckerPolynomialBoxExists := by
  intro K _ n p
  let M := Finset.univ.sup (fun i : Fin n => p.degreeOf i)
  refine ⟨2 + M, by omega, ?_⟩
  apply (box_iff_degreeOf p (by omega)).mpr
  intro i
  have hi : p.degreeOf i ≤ M := Finset.le_sup (f := fun j : Fin n => p.degreeOf j)
    (Finset.mem_univ i)
  omega

theorem product_box : Targets.kroneckerPolynomialProductBox := by
  intro K _ n B hB p h hp hh
  apply (box_iff_degreeOf (p * h) (by omega)).mpr
  intro i
  have hpi := (box_iff_degreeOf p (by omega)).mp hp i
  have hhi := (box_iff_degreeOf h (by omega)).mp hh i
  have hprod := MvPolynomial.degreeOf_mul_le i p h
  omega

theorem quotient_box : Targets.kroneckerPolynomialQuotientBox := by
  intro K _ n B hB p q h hp hq hqbox
  classical
  by_cases hh : h = 0
  · subst h
    intro d hd
    simp only [MvPolynomial.support_zero, Finset.notMem_empty] at hd
  · apply (box_iff_degreeOf h (by omega)).mpr
    intro i
    have hqi := (box_iff_degreeOf q (by omega)).mp hqbox i
    rw [hq, MvPolynomial.degreeOf_mul_eq hp hh] at hqi
    omega

theorem larger_base_verification : Targets.kroneckerPolynomialLargerBaseVerification := by
  intro K _ n B hB p h q hp hh hq
  have hprod := product_box K n B hB p h hp hh
  have hq' : Box (2 * B) q := by
    intro d hd i
    have hi := hq d hd i
    omega
  constructor
  · intro heq
    apply polynomial_injective K n (2 * B) (by omega) (p * h) q hprod hq'
    simpa only [map_mul] using heq
  · intro heq
    rw [← map_mul, heq]

end LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial
