module
public import LogicLineages.CartierObserverCurrent.RationalCoverageTargets
public import LogicLineages.CartierObserverCurrent.RootInterpolationProof
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public import Mathlib.Algebra.BigOperators.Field
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RationalCoverage
open SplittingRoots RootInterpolation Polynomial

private noncomputable instance rootFintype (d : Nat) : Fintype (Root d) := by
  classical
  unfold Root
  infer_instance

private theorem product_ne_zero (d : Nat) : rootProduct d ≠ 0 := (productDegree d).1.ne_zero

private theorem fraction_injective (d : Nat) : Function.Injective (fraction d) := by
  intro U V h
  apply RatFunc.algebraMap_injective
  exact (div_left_inj' (RatFunc.algebraMap_ne_zero (product_ne_zero d))).mp h

theorem statePresentation : Targets.StatePresentation := by
  intro d f
  constructor
  · rintro ⟨hproper, q, hq⟩
    have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hq; exact product_ne_zero d hq
    refine ⟨f.num * q, ?_, ?_⟩
    · by_cases hf : f = 0
      · simp only [hf, RatFunc.num_zero, zero_mul, degree_zero]
        exact WithBot.bot_lt_iff_ne_bot.mpr (mt degree_eq_bot.mp (product_ne_zero d))
      · change f.num.degree < f.denom.degree at hproper
        rw [degree_eq_natDegree (RatFunc.num_ne_zero hf), degree_eq_natDegree f.denom_ne_zero] at hproper
        rw [hq, degree_eq_natDegree (mul_ne_zero (RatFunc.num_ne_zero hf) hq0),
          degree_eq_natDegree (mul_ne_zero f.denom_ne_zero hq0),
          natDegree_mul (RatFunc.num_ne_zero hf) hq0, natDegree_mul f.denom_ne_zero hq0]
        exact WithBot.coe_lt_coe.mpr (Nat.add_lt_add_right (WithBot.coe_lt_coe.mp hproper) _)
    · unfold fraction
      rw [hq, map_mul, map_mul, mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero hq0)]
      exact f.num_div_denom.symm
  · rintro ⟨U, hU, rfl⟩
    exact ⟨MixedProper.fractionProper _ _ _ hU, RatFunc.denom_div_dvd _ _⟩

theorem numeratorDegree : Targets.NumeratorDegree := by
  intro d b
  classical
  unfold tupleNumerator
  rw [degree_eq_natDegree (product_ne_zero d), (productDegree d).2]
  apply (degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro z _
  have h := degree_smul_le (b z) (omittedProduct d z.val)
  rw [smul_eq_C_mul] at h
  exact h.trans_lt (omittedDegree d z)

private theorem other_eval (d : Nat) (z a : Root d) (ha : a ≠ z) :
    (omittedProduct d a.val).eval z.val = 0 := by
  classical
  simp only [omittedProduct, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨?_, z.property⟩)
  · exact sub_self _
  · intro h
    exact ha (Subtype.ext h.symm)

theorem numeratorEvaluation : Targets.NumeratorEvaluation := by
  intro d b z
  classical
  simp only [tupleNumerator, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_eq_single z]
  · intro a _ ha
    rw [other_eval d z a ha, mul_zero]
  · simp

private theorem embed_C (d : Nat) (x : FieldAt d) :
    algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) (C x) =
      algebraMap (FieldAt d) (RatFunc (FieldAt d)) x := by
  exact (IsScalarTower.algebraMap_apply (FieldAt d) (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) x).symm

theorem actualPartialFraction : Targets.ActualPartialFraction := by
  intro d b
  classical
  unfold reconstruct fraction tupleNumerator
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_mul, embed_C, omittedFactor d z, map_mul, map_sub, embed_C]
  change _ = _ / ((Basic.rationalX - _) * _)
  exact (mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero
    (show omittedProduct d z.val ≠ 0 from fun h => by
      have he := omittedNonzero d z
      apply he
      rw [h, eval_zero]))).symm

theorem reconstructionInjective : Targets.ReconstructionInjective := by
  intro d b c h
  rw [actualPartialFraction, actualPartialFraction] at h
  have hn := fraction_injective d h
  funext z
  have he := congrArg (fun P : Polynomial (FieldAt d) => P.eval z.val) hn
  rw [numeratorEvaluation, numeratorEvaluation] at he
  exact (mul_right_cancel₀ (omittedNonzero d z)) he

private theorem numerator_residues (d : Nat) (U : Polynomial (FieldAt d)) :
    tupleNumerator d (residues d U) = interpolate d U := by
  classical
  unfold tupleNumerator residues interpolate
  exact Finset.sum_coe_sort (SplittingRoots.rootSet d)
    (fun z => C (U.eval z / (omittedProduct d z).eval z) * omittedProduct d z)

theorem reconstructionCoverage : Targets.ReconstructionCoverage := by
  intro d f
  constructor
  · intro hf
    obtain ⟨U, hU, rfl⟩ := (statePresentation d f).mp hf
    have hcard : U.degree < ((SplittingRoots.rootSet d).card : WithBot Nat) := by
      simpa [degree_eq_natDegree (product_ne_zero d), (productDegree d).2] using hU
    have he : reconstruct d (residues d U) = fraction d U := by
      rw [actualPartialFraction, numerator_residues, interpolationComplete d U hcard]
    refine ⟨residues d U, he, ?_⟩
    intro b hb
    exact reconstructionInjective d (hb.trans he.symm)
  · rintro ⟨b, hb, _⟩
    apply (statePresentation d f).mpr
    exact ⟨tupleNumerator d b, numeratorDegree d b, hb.symm.trans (actualPartialFraction d b)⟩

#audit_namespace LogicLineages.CartierObserverCurrent.RationalCoverage
end LogicLineages.CartierObserverCurrent.RationalCoverage
