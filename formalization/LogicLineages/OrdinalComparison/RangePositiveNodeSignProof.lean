module
public import LogicLineages.OrdinalComparison.RangePositiveNodeTailProof
public import LogicLineages.OrdinalComparison.RangePositiveNodeSourceProof
public import LogicLineages.OrdinalComparison.RangePositiveNodeQueryProof
public import LogicLineages.OrdinalComparison.CollectedRangeCellsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

private theorem entry_direct (tags : CollectedPositiveTags) (rho : NONote) (B : CollectedPositiveNF) (a : Nat)
    (hm : (rho,B,a)∈collectedTagEntries tags) : (rho,B)∈collectedDirectTags tags := by
  cases tags with
  | nil => cases hm
  | cons sigma C c rest =>
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (entry_direct rest rho B a hm)
termination_by tags

theorem sign_stable (q : ComparisonQuery) (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range w A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (hq : RootOrientations q w A P) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (profile x y : Nat) (hxT : encodedComparisonTableTail table≤x) (hyT : encodedComparisonTableTail table≤y)
    (hx : encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) profile≤x)
    (hy : encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) profile≤y) :
    comparisonNaturalSign (actualOneVariableComparisonValue (.range w A) x) (actualFixedLimitProfileEval P x)=
      comparisonNaturalSign (actualOneVariableComparisonValue (.range w A) y) (actualFixedLimitProfileEval P y) := by
  rw [←collectedPositiveNormalizeValue P hP x,←collectedPositiveNormalizeValue P hP y]
  cases hNF : collectedPositiveNormalize P with
  | mk c b tags =>
    cases tags with
    | nil =>
      have hAff := RangeAffineProgram.actual_program.2 w A hR b c
      have hxAff := (hAff.2 x ((local_affine_bound _ P hP profile c b .nil hNF).trans hx)).2
      have hyAff := (hAff.2 y ((local_affine_bound _ P hP profile c b .nil hNF).trans hy)).2
      have hx' : actualCollectedPositiveEval (.mk c b .nil) x<actualOneVariableComparisonValue (.range w A) x := by
        simpa only [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.add_zero,Nat.add_comm c (b*x)] using hxAff
      have hy' : actualCollectedPositiveEval (.mk c b .nil) y<actualOneVariableComparisonValue (.range w A) y := by
        simpa only [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.add_zero,Nat.add_comm c (b*y)] using hyAff
      exact ((ComparisonNode.natural_sign _ _).2.2.2.mpr hx').trans
        ((ComparisonNode.natural_sign _ _).2.2.2.mpr hy').symm
    | cons rho B a rest =>
      let tags : CollectedPositiveTags := .cons rho B a rest
      have hTags : CollectedTagsValid tags := by
        have h := collectedPositiveNormalizeValid P hP
        rw [hNF] at h
        exact h
      have hn : tags≠.nil := by
        change CollectedPositiveTags.cons rho B a rest≠.nil
        intro h
        cases h
      have hPx : collectedRangeThreshold (.mk c b tags)≤x := by
        have h := (local_range_bound _ P hP profile).trans hx
        simpa only [hNF,tags] using h
      have hPy : collectedRangeThreshold (.mk c b tags)≤y := by
        have h := (local_range_bound _ P hP profile).trans hy
        simpa only [hNF,tags] using h
      have hDx : oneVariableComparisonDomainAt (.range w A) x :=
        ((OneVariableComparison.source_program.2.2 (.range w A) hR).2.2 x (by
          rw [←(OneVariableComparison.source_program.2.2 (.range w A) hR).1]
          exact (local_domain_bound _ _ profile).trans hx)).1
      have hDy : oneVariableComparisonDomainAt (.range w A) y :=
        ((OneVariableComparison.source_program.2.2 (.range w A) hR).2.2 y (by
          rw [←(OneVariableComparison.source_program.2.2 (.range w A) hR).1]
          exact (local_domain_bound _ _ profile).trans hy)).1
      have hCellX := collectedRangeCellTests c b tags hTags hn x hPx _ (range_image w A hR x hDx)
      have hCellY := collectedRangeCellTests c b tags hTags hn y hPy _ (range_image w A hR y hDy)
      have hLe : ∀ sigma C d,(sigma,C,d)∈collectedTagEntries tags →
          (actualOneVariableComparisonValue (.range w A) x≤actualCollectedTagPeak sigma C x ↔
            actualOneVariableComparisonValue (.range w A) y≤actualCollectedTagPeak sigma C y) := by
        intro sigma C d hm
        have hr : (sigma,C)∈collectedSourceRootTags (collectedPositiveNormalize P) := by
          rw [hNF]
          exact entry_direct tags sigma C d hm
        exact root_peak_order_stable q w A P hR hP hq table hc sigma C hr x y hxT hyT
      have hLt : actualOneVariableComparisonValue (.range w A) x<actualCollectedPositiveEval (.mk c b tags) x ↔
          actualOneVariableComparisonValue (.range w A) y<actualCollectedPositiveEval (.mk c b tags) y := by
        constructor
        · intro h
          obtain ⟨sigma,C,d,hm,hs⟩ := hCellX.1.mp h
          exact hCellY.1.mpr ⟨sigma,C,d,hm,(hLe sigma C d hm).mp hs⟩
        · intro h
          obtain ⟨sigma,C,d,hm,hs⟩ := hCellY.1.mp h
          exact hCellX.1.mpr ⟨sigma,C,d,hm,(hLe sigma C d hm).mpr hs⟩
      have hGt : actualCollectedPositiveEval (.mk c b tags) x<actualOneVariableComparisonValue (.range w A) x ↔
          actualCollectedPositiveEval (.mk c b tags) y<actualOneVariableComparisonValue (.range w A) y := by
        have hnX := hCellX.2.2
        have hnY := hCellY.2.2
        omega
      change comparisonNaturalSign (actualOneVariableComparisonValue (.range w A) x)
        (actualCollectedPositiveEval (.mk c b tags) x)=
          comparisonNaturalSign (actualOneVariableComparisonValue (.range w A) y)
            (actualCollectedPositiveEval (.mk c b tags) y)
      unfold comparisonNaturalSign
      simp only [hLt,hGt]

end LogicLineages.OrdinalComparison.RangePositiveNode
