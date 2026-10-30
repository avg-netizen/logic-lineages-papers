module
public import LogicLineages.OrdinalComparison.CartierProperTargets
public import LogicLineages.OrdinalComparison.CartierRationalProof

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualRationalProperDegree : Targets.ActualRationalProperDegree.{u} := by
  intro K _ f
  by_cases hf : f = 0
  · simp [hf, actualRationalProper]
  · unfold actualRationalProper RatFunc.intDegree
    rw [Polynomial.degree_eq_natDegree (RatFunc.num_ne_zero hf),
      Polynomial.degree_eq_natDegree f.denom_ne_zero]
    simp only [Nat.cast_lt, hf, false_or]
    omega

private theorem degree_add_lower {K : Type*} [Field K] (x y : RatFunc K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hne : x.intDegree ≠ y.intDegree) :
    max x.intDegree y.intDegree ≤ (x + y).intDegree := by
  have h1 : x.intDegree ≤ max (x + y).intDegree y.intDegree := by
    have h := RatFunc.intDegree_add_le (x := x + y) (y := -y) (neg_ne_zero.mpr hy)
      (by simpa using hx)
    simpa only [add_neg_cancel_right, RatFunc.intDegree_neg] using h
  have h2 : y.intDegree ≤ max (x + y).intDegree x.intDegree := by
    have he : (x + y) + -x = y := by ring
    have h := RatFunc.intDegree_add_le (x := x + y) (y := -x) (neg_ne_zero.mpr hx)
      (by rw [he]; exact hy)
    simpa only [he, RatFunc.intDegree_neg] using h
  omega

theorem actualDifferentialCartierProper : Targets.ActualDifferentialCartierProper.{u} := by
  intro K _ _ _ f hf
  rw [actualRationalProperDegree K] at hf ⊢
  let a := actualRationalSquareRootDigit false f
  let b := actualRationalSquareRootDigit true f
  change b = 0 ∨ b.intDegree < 0
  by_cases hb : b = 0
  · exact Or.inl hb
  right
  have hdec : f = a ^ 2 + RatFunc.X * b ^ 2 := actualRationalSquareRootDecomposition K f
  have hf0 : f ≠ 0 := by
    intro hz
    have hzero := actualRationalSquareRootUniqueness K a b 0 0
      (by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hdec.symm.trans hz)
    exact hb hzero.2
  have hdf : f.intDegree < 0 := hf.resolve_left hf0
  have hdb : (RatFunc.X * b ^ 2).intDegree = 1 + 2 * b.intDegree := by
    rw [RatFunc.intDegree_mul RatFunc.X_ne_zero (pow_ne_zero _ hb), pow_two,
      RatFunc.intDegree_mul hb hb, RatFunc.intDegree_X]
    omega
  by_cases ha : a = 0
  · have he : f = RatFunc.X * b ^ 2 := by simpa [ha] using hdec
    rw [he, hdb] at hdf
    omega
  · have hda : (a ^ 2).intDegree = 2 * a.intDegree := by
      rw [pow_two, RatFunc.intDegree_mul ha ha]
      omega
    have hne : (a ^ 2).intDegree ≠ (RatFunc.X * b ^ 2).intDegree := by rw [hda, hdb]; omega
    have hlow := degree_add_lower (a ^ 2) (RatFunc.X * b ^ 2) (pow_ne_zero _ ha)
      (mul_ne_zero RatFunc.X_ne_zero (pow_ne_zero _ hb)) hne
    rw [← hdec, hda, hdb] at hlow
    omega

theorem actualDifferentialCartierIterateProper : Targets.ActualDifferentialCartierIterateProper.{u} := by
  intro K _ _ _ f hf j
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact actualDifferentialCartierProper K _ ih

end LogicLineages.OrdinalComparison
