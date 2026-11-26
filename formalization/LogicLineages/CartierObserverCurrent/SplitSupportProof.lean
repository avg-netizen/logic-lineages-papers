module
public import LogicLineages.CartierObserverCurrent.SplitSupportTargets
public import LogicLineages.CartierObserverCurrent.RootInterpolationProof
public import LogicLineages.CartierObserverCurrent.SplittingRootsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplitSupport
open SplittingRoots RootInterpolation Polynomial

theorem productRoots : Targets.ProductRoots := by
  intro d
  classical
  exact roots_prod_X_sub_C _

theorem splitDivisibility : Targets.SplitDivisibility := by
  intro d Q hQ hsplit
  classical
  rw [hsplit.dvd_iff_roots_le_roots hQ (productDegree d).1.ne_zero, productRoots d]
  constructor
  · intro h
    constructor
    · intro z hz
      exact Multiset.subset_of_le h ((mem_roots hQ).mpr hz)
    · intro z
      rw [← count_roots]
      exact (Multiset.count_le_of_le z h).trans
        (Multiset.nodup_iff_count_le_one.mp (SplittingRoots.rootSet d).nodup z)
  · rintro ⟨hsupport, hsimple⟩
    apply Multiset.le_iff_count.mpr
    intro z
    by_cases hz : z ∈ Q.roots
    · have hs : z ∈ (SplittingRoots.rootSet d).val := hsupport z ((mem_roots hQ).mp hz)
      rw [Multiset.count_eq_one_of_mem (SplittingRoots.rootSet d).nodup hs, count_roots]
      exact hsimple z
    · rw [Multiset.count_eq_zero_of_notMem hz]
      exact Nat.zero_le _

theorem sourceSimpleDivisor : Targets.SourceSimpleDivisor := by
  intro d Q hQ hdiv hsimple
  have hA : splitPolynomial d ≠ 0 := by
    intro h
    have he : (splitPolynomial d).eval 0 = 1 := by
      simp [splitPolynomial, SourceBudget.denominator, Polynomial.map_prod, Polynomial.eval_prod]
    rw [h, eval_zero] at he
    exact zero_ne_one he
  have hs := (actualSplitting d).of_dvd hA hdiv
  apply (splitDivisibility d Q hQ hs).mpr
  refine ⟨?_, hsimple⟩
  intro z hz
  apply (exactAllRoots d z).mpr
  obtain ⟨R, hR⟩ := hdiv
  rw [hR, eval_mul, hz, zero_mul]

#audit_namespace LogicLineages.CartierObserverCurrent.SplitSupport
end LogicLineages.CartierObserverCurrent.SplitSupport
