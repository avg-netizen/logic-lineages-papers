module
public import LogicLineages.OrdinalComparison.PrimitiveRootComplementTargets
public import LogicLineages.OrdinalComparison.PrimitiveRootProductProof
public import LogicLineages.OrdinalComparison.BinaryPeriodSuppliersProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

private theorem source_eval_range {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (m : Nat) (z : K) :
    Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator m) =
      ∏ i ∈ Finset.range m, (1 + z ^ (i + 1)) := by
  unfold actualBinarySourceDenominator
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X_pow]
  exact (Finset.prod_range (fun i : Nat => 1 + z ^ (i + 1))).symm

theorem actualPrimitiveRootComplement : Targets.ActualPrimitiveRootComplement.{u} := by
  intro K _ _ q m hodd hmq z hz
  have hq : 0 < q := by omega
  have hz0 : z ≠ 0 := (hz.isUnit hq.ne').ne_zero
  let a := q - 1 - m
  have ha : a + m = q - 1 := by dsimp [a]; omega
  have hsplit :
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator (q - 1)) =
        Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator a) *
        Polynomial.eval₂ (algebraMap (ZMod 2) K) z⁻¹ (actualBinarySourceDenominator m) := by
    rw [source_eval_range, ← ha, Finset.prod_range_add, source_eval_range, source_eval_range]
    congr 1
    rw [← Finset.prod_range_reflect (fun j : Nat => 1 + z ^ (a + j + 1)) m]
    apply Finset.prod_congr rfl
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hexp : a + (m - 1 - j) + 1 = q - (j + 1) := by dsimp [a]; omega
    rw [hexp]
    have hp : z ^ (q - (j + 1)) = (z ^ (j + 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, Nat.sub_add_cancel (by omega : j + 1 ≤ q), hz.pow_eq_one]
    rw [hp, inv_pow]
  have hunit :
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator a) *
      Polynomial.eval₂ (algebraMap (ZMod 2) K) z⁻¹ (actualBinarySourceDenominator m) = 1 := by
    rw [← hsplit]
    exact actualPrimitiveRootCompleteProduct K q hodd z hz
  have hinv := inv_eq_of_mul_eq_one_right hunit
  change (Polynomial.eval₂ (algebraMap (ZMod 2) K) z (actualBinarySourceDenominator a))⁻¹ = _
  rw [hinv, actualBinarySourceReciprocity K m z hz0]

end LogicLineages.OrdinalComparison
