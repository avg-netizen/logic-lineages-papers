module
public import LogicLineages.OrdinalComparison.RangePositiveNodeGapProof
public import LogicLineages.OrdinalComparison.ComparisonNodeStepProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

attribute [local irreducible] encodedRangePositiveLocalTail encodedSourcePairSignAt

theorem range_correct : Targets.ActualRangePositiveQueryNodeCorrect := by
  intro w A P hR hP leftProfile rightProfile table
  dsimp only
  intro hc
  let q : ComparisonQuery := ((oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (.positive P)),
    (leftProfile,rightProfile))
  let N := max (encodedComparisonTableTail table)
    (encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) leftProfile)
  have hmR : oneVariableComparisonEncode (.range w A)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  have hdP : oneVariableComparisonEncode (.positive P)/2=positiveExprEncode P := by
    change (2*positiveExprEncode P)/2=positiveExprEncode P
    omega
  have hresult : encodedRangePositiveQueryNode q table=
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.range w A)) (oneVariableComparisonEncode (.positive P)) N,N) := by
    simp only [encodedRangePositiveQueryNode,q,hmR,Nat.one_ne_zero,if_false,hdP,N]
  rw [hresult]
  have hNT : encodedComparisonTableTail table≤N := Nat.le_max_left _ _
  have hNL : encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) leftProfile≤N := Nat.le_max_right _ _
  have hN1 : 1≤N := (ComparisonNode.table_tail_positive table).trans hNT
  have hDom : oneVariableComparisonDomainBound (.range w A)≤N := by
    rw [←(OneVariableComparison.source_program.2.2 _ hR).1]
    exact (local_domain_bound _ _ leftProfile).trans hNL
  have hq : RootOrientations q w A P := Or.inl rfl
  have hs : comparisonEventualSignData (.range w A) (.positive P)
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.range w A)) (oneVariableComparisonEncode (.positive P)) N,N) :=
    ComparisonNode.point_tail_from_stable (.range w A) (.positive P) hR hP N hN1 hDom hN1
      (fun x hx => sign_stable q w A P hR hP hq table hc leftProfile x N
        (hNT.trans hx) hNT (hNL.trans hx) hNL)
  intro E F hEc hFc hEV hFV
  have hEq : E=.range w A := ComparisonExpansion.source_injective hEc
  have hFq : F=.positive P := ComparisonExpansion.source_injective hFc
  subst E F
  refine ⟨hs,?_,?_⟩
  · intro hSig
    exact requested_gap q w A P hR hP hq table hc leftProfile N (by simp [q]) hNT hNL
      (fun x hx => (hs.2.2 x hx).2.2.2.2.mp hSig)
  · intro _ word eta mass B hbad
    cases hbad

theorem positive_range_correct : Targets.ActualPositiveRangeQueryNodeCorrect := by
  intro w P A hP hR leftProfile rightProfile table
  dsimp only
  intro hc
  let q : ComparisonQuery := ((oneVariableComparisonEncode (.positive P),oneVariableComparisonEncode (.range w A)),
    (leftProfile,rightProfile))
  let N := max (encodedComparisonTableTail table)
    (encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) rightProfile)
  have hmP : oneVariableComparisonEncode (.positive P)%2=0 := by
    change (2*positiveExprEncode P)%2=0
    omega
  have hdP : oneVariableComparisonEncode (.positive P)/2=positiveExprEncode P := by
    change (2*positiveExprEncode P)/2=positiveExprEncode P
    omega
  have hresult : encodedRangePositiveQueryNode q table=
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.positive P)) (oneVariableComparisonEncode (.range w A)) N,N) := by
    simp only [encodedRangePositiveQueryNode,q,hmP,if_true,hdP,N]
  rw [hresult]
  have hNT : encodedComparisonTableTail table≤N := Nat.le_max_left _ _
  have hNL : encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range w A)) (positiveExprEncode P) rightProfile≤N := Nat.le_max_right _ _
  have hN1 : 1≤N := (ComparisonNode.table_tail_positive table).trans hNT
  have hDom : oneVariableComparisonDomainBound (.range w A)≤N := by
    rw [←(OneVariableComparison.source_program.2.2 _ hR).1]
    exact (local_domain_bound _ _ rightProfile).trans hNL
  have hq : RootOrientations q w A P := Or.inr rfl
  have hs : comparisonEventualSignData (.positive P) (.range w A)
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.positive P)) (oneVariableComparisonEncode (.range w A)) N,N) :=
    ComparisonNode.point_tail_from_stable (.positive P) (.range w A) hP hR N hN1 hN1 hDom (fun x hx =>
      ComparisonNode.natural_sign_swap _ _ _ _ (sign_stable q w A P hR hP hq table hc rightProfile x N
        (hNT.trans hx) hNT (hNL.trans hx) hNL))
  intro E F hEc hFc hEV hFV
  have hEq : E=.positive P := ComparisonExpansion.source_injective hEc
  have hFq : F=.range w A := ComparisonExpansion.source_injective hFc
  subst E F
  refine ⟨hs,?_,?_⟩
  · intro _ word eta mass B hbad
    cases hbad
  · intro hSig
    exact requested_gap q w A P hR hP hq table hc rightProfile N (by simp [q]) hNT hNL
      (fun x hx => (hs.2.2 x hx).2.2.1.mp hSig)

theorem full : Targets.FullActualRangePositiveQueryNode :=
  ⟨open_growth,range_image,program,range_correct,positive_range_correct⟩

end LogicLineages.OrdinalComparison.RangePositiveNode
