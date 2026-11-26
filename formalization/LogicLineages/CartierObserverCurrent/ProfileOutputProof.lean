module
public import LogicLineages.CartierObserverCurrent.ProfileOutputTargets
public import LogicLineages.CartierObserverCurrent.ProfileDescentProof
public import Mathlib.Algebra.BigOperators.Field
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.ProfileOutput
open SplittingRoots RootInterpolation Polynomial

private noncomputable instance rootFintype (d : Nat) : Fintype (Root d) := by
  classical
  unfold Root
  infer_instance

theorem productRegular : Targets.ProductRegular := by
  intro d
  classical
  simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact neg_ne_zero.mpr (nonzeroRoots d ⟨z, hz⟩)

theorem numeratorRatio : Targets.NumeratorRatio := by
  intro d b
  classical
  unfold RationalCoverage.tupleNumerator value
  rw [eval_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  have ht : (rootProduct d).eval 0 = z.val * (omittedProduct d z.val).eval 0 := by
    rw [omittedFactor d z, eval_mul, eval_sub, eval_X, eval_C, zero_sub, CharTwo.neg_eq]
  have hD : (omittedProduct d z.val).eval 0 ≠ 0 := by
    intro h
    apply productRegular d
    rw [ht, h, mul_zero]
  rw [eval_mul, eval_C, ht, mul_div_mul_right _ _ hD]

private theorem series_constant {K : Type u} [Field K] (P Q : Polynomial K) :
    (FractionSeries.seriesFraction P Q).coeff 0 = P.eval 0 / Q.eval 0 := by
  simp [FractionSeries.seriesFraction, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, div_eq_mul_inv]

theorem actualSeriesOutput : Targets.ActualSeriesOutput := by
  intro d b
  rw [series_constant, numeratorRatio]

theorem actualBaseOutput : Targets.ActualBaseOutput := by
  intro d g b hg
  let σ := algebraMap (ZMod 2) (FieldAt d)
  let f := ProfileDescent.extend d g
  have hstate : RationalCoverage.state d f := by
    apply (RationalCoverage.statePresentation d _).mpr
    exact ⟨RationalCoverage.tupleNumerator d b, RationalCoverage.numeratorDegree d b,
      hg.trans (RationalCoverage.actualPartialFraction d b)⟩
  have hd0 : f.denom.eval 0 ≠ 0 := by
    obtain ⟨Q, hQ⟩ := hstate.2
    intro h
    apply productRegular d
    rw [hQ, eval_mul, h, zero_mul]
  have hdn : f.denom = g.denom.map σ := CanonicalExtension.denominatorMap _ _ σ g
  have hnn : f.num = g.num.map σ := CanonicalExtension.numeratorMap _ _ σ g
  have hdmap : f.denom.eval 0 = σ (g.denom.eval 0) := by
    rw [hdn]
    simpa using Polynomial.eval_map_apply σ (p := g.denom) 0
  have hnmap : f.num.eval 0 = σ (g.num.eval 0) := by
    rw [hnn]
    simpa using Polynomial.eval_map_apply σ (p := g.num) 0
  have hbase0 : g.denom.eval 0 ≠ 0 := by
    intro h
    apply hd0
    rw [hdmap, h, map_zero]
  refine ⟨hbase0, ?_⟩
  rw [series_constant, map_div₀]
  change σ (g.num.eval 0) / σ (g.denom.eval 0) = _
  rw [← hnmap, ← hdmap, ← numeratorRatio d b]
  apply (div_eq_div_iff hd0 (productRegular d)).mpr
  have hfrac : f = RationalCoverage.fraction d (RationalCoverage.tupleNumerator d b) :=
    hg.trans (RationalCoverage.actualPartialFraction d b)
  have hc := (RatFunc.num_mul_eq_mul_denom_iff (productDegree d).1.ne_zero).mpr hfrac
  simpa only [eval_mul] using congrArg (fun P : Polynomial (FieldAt d) => P.eval 0) hc

theorem outputDescent : Targets.OutputDescent := by
  intro d b hb
  obtain ⟨g, ⟨_, hg⟩, _⟩ := (ProfileDescent.profileToBase d b).mp hb
  have ho := (actualBaseOutput d g b hg).2
  refine ⟨(FractionSeries.seriesFraction g.num g.denom).coeff 0, ho, ?_⟩
  intro a ha
  exact (algebraMap (ZMod 2) (FieldAt d)).injective (ha.trans ho.symm)

#audit_namespace LogicLineages.CartierObserverCurrent.ProfileOutput
end LogicLineages.CartierObserverCurrent.ProfileOutput
