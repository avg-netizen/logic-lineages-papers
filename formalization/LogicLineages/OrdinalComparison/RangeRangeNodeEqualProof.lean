module
public import LogicLineages.OrdinalComparison.RangeRangeNodeEqualTargets
public import LogicLineages.OrdinalComparison.RangeRangeNodeEqualGapProof
public import LogicLineages.OrdinalComparison.ComparisonNodeStepProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem equal_correct : Targets.ActualSameOuterRangeQueryNodeCorrect := by
  intro w v eta c d E F hR hS leftProfile rightProfile table
  dsimp only
  intro hc
  let q : ComparisonQuery := ((oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
    oneVariableComparisonEncode (.range (v++[(eta,d)]) F)),(leftProfile,rightProfile))
  let N := max (encodedComparisonTableTail table) (encodedRangeRangeLocalTail q)
  have hresult : encodedRangeRangeQueryNode q table=
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
        (oneVariableComparisonEncode (.range (v++[(eta,d)]) F)) N,N) := rfl
  rw [hresult]
  have hNT : encodedComparisonTableTail table≤N := Nat.le_max_left _ _
  have hNL : encodedRangeRangeLocalTail q≤N := Nat.le_max_right _ _
  have hN1 : 1≤N := (ComparisonNode.table_tail_positive table).trans hNT
  have hDomR : oneVariableComparisonDomainBound (.range (w++[(eta,c)]) E)≤N := by
    rw [←(OneVariableComparison.source_program.2.2 _ hR).1]
    exact (left_domain_bound q).trans hNL
  have hDomS : oneVariableComparisonDomainBound (.range (v++[(eta,d)]) F)≤N := by
    rw [←(OneVariableComparison.source_program.2.2 _ hS).1]
    exact (right_domain_bound q).trans hNL
  have hs : comparisonEventualSignData (.range (w++[(eta,c)]) E) (.range (v++[(eta,d)]) F)
      (encodedSourcePairSignAt (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
        (oneVariableComparisonEncode (.range (v++[(eta,d)]) F)) N,N) :=
    ComparisonNode.point_tail_from_stable _ _ hR hS N hN1 hDomR hDomS (fun x hx =>
      equal_sign_stable q w v eta c d E F hR hS rfl table hc x N (hNT.trans hx) hNT (hNL.trans hx) hNL)
  intro E' F' hEc hFc hEV hFV
  have hEq : E'=.range (w++[(eta,c)]) E := ComparisonExpansion.source_injective hEc
  have hFq : F'=.range (v++[(eta,d)]) F := ComparisonExpansion.source_injective hFc
  subst E' F'
  refine ⟨hs,?_,?_⟩
  · intro hSig
    exact equal_left_gap q w v eta c d E F hR hS rfl leftProfile N (by simp [q]) hNL
      (fun x hx => (hs.2.2 x hx).2.2.2.2.mp hSig)
  · intro hSig
    exact equal_right_gap q w v eta c d E F hR hS rfl rightProfile N (by simp [q]) hNL
      (fun x hx => (hs.2.2 x hx).2.2.1.mp hSig)

end LogicLineages.OrdinalComparison.RangeRangeNode
