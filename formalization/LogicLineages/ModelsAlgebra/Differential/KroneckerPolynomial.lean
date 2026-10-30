module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomialTargets
public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndex
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial

variable {K : Type*} [CommRing K]

private theorem exponent_apply (B n k : ℕ) (i : Fin n) :
    exponent B n k i = KroneckerIndex.digits B n k i := rfl

private theorem exponent_index (n B k : ℕ) (hB : 2 ≤ B) (hk : k < B ^ n) :
    KroneckerIndex.index B (exponent B n k) = k :=
  KroneckerIndex.index_digits n B k hB hk

theorem monomial_encoding : Targets.kroneckerPolynomialMonomial := by
  intro K _ n B d a
  simp only [encode, MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

private theorem encode_sum {n : ℕ} (B : ℕ) (p : MvPolynomial (Fin n) K) :
    encode B p = ∑ d ∈ p.support, Polynomial.C (p.coeff d) *
      Polynomial.X ^ KroneckerIndex.index B d := by
  calc
    encode B p = encode B (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) :=
      congrArg (encode B) p.as_sum
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact monomial_encoding K n B d (p.coeff d)

theorem coefficient_calibration : Targets.kroneckerPolynomialCoefficient := by
  intro K _ n B hB p d hp hd
  classical
  rw [encode_sum, Polynomial.finsetSum_coeff]
  have hs : (∑ e ∈ p.support,
      (Polynomial.C (p.coeff e) * Polynomial.X ^ KroneckerIndex.index B e).coeff
        (KroneckerIndex.index B d)) =
      ∑ e ∈ p.support, if d = e then p.coeff e else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Polynomial.coeff_C_mul_X_pow]
    have hiff : KroneckerIndex.index B d = KroneckerIndex.index B e ↔ d = e := by
      constructor
      · intro h
        have hf := KroneckerIndex.index_injective n B hB d e hd (hp e he) h
        exact Finsupp.ext (fun i => congrFun hf i)
      · rintro rfl
        rfl
    simp only [hiff]
  rw [hs]
  by_cases hdmem : d ∈ p.support
  · rw [Finset.sum_eq_single d]
    · simp
    · intro e _ hed
      simp [Ne.symm hed]
    · intro hnot
      exact False.elim (hnot hdmem)
  · rw [MvPolynomial.notMem_support_iff.mp hdmem]
    apply Finset.sum_eq_zero
    intro e he
    by_cases hde : d = e
    · exact False.elim (hdmem (hde.symm ▸ he))
    · rw [if_neg hde]

theorem degree_bound : Targets.kroneckerPolynomialDegreeBound := by
  intro K _ n B hB p hp
  rw [encode_sum]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
  apply (Finset.sup_lt_iff (show 0 < B ^ n from pow_pos (by omega) n)).mpr
  intro d hd
  have hm : (Polynomial.C (p.coeff d) * Polynomial.X ^ KroneckerIndex.index B d).natDegree ≤
      KroneckerIndex.index B d := by
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.natDegree_monomial_le _
  exact hm.trans_lt (KroneckerIndex.index_bound n B hB d (hp d hd))

theorem polynomial_injective : Targets.kroneckerPolynomialInjective := by
  intro K _ n B hB p q hp hq heq
  classical
  ext d
  by_cases hd : KroneckerIndex.Bounded B d
  · rw [← coefficient_calibration K n B hB p d hp hd,
      ← coefficient_calibration K n B hB q d hq hd, heq]
  · have hzp : p.coeff d = 0 := by
      by_contra hnonzero
      exact hd (hp d (MvPolynomial.mem_support_iff.mpr hnonzero))
    have hzq : q.coeff d = 0 := by
      by_contra hnonzero
      exact hd (hq d (MvPolynomial.mem_support_iff.mpr hnonzero))
    rw [hzp, hzq]

theorem decoded_box : Targets.kroneckerDecodedBox := by
  intro K _ n B hB q d hd
  classical
  by_contra hnot
  have hzero : (decode B n q).coeff d = 0 := by
    rw [decode, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [MvPolynomial.coeff_monomial]
    apply if_neg
    intro heq
    apply hnot
    rw [← heq]
    exact KroneckerIndex.digits_bound n B k hB
  exact (MvPolynomial.mem_support_iff.mp hd) hzero

theorem encode_decode : Targets.kroneckerPolynomialEncodeDecode := by
  intro K _ n B hB q hq
  rw [decode, map_sum]
  calc
    _ = ∑ k ∈ Finset.range (B ^ n), Polynomial.C (q.coeff k) * Polynomial.X ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [monomial_encoding K n B, exponent_index n B k hB (Finset.mem_range.mp hk)]
    _ = q := (q.as_sum_range_C_mul_X_pow' hq).symm

theorem decode_encode : Targets.kroneckerPolynomialDecodeEncode := by
  intro K _ n B hB p hp
  apply polynomial_injective K n B hB _ p
    (decoded_box K n B hB (encode B p)) hp
  exact encode_decode K n B hB (encode B p) (degree_bound K n B hB p hp)

end LogicLineages.ModelsAlgebra.Differential.KroneckerPolynomial
