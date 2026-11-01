module
public import LogicLineages.OrdinalComparison.RangeRangeNodeEqualSignProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem equal_left_gap (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F)))
    (profile N : Nat) (hprofile : profile∈[q.2.1,q.2.2,1]) (hN : encodedRangeRangeLocalTail q≤N)
    (hWin : ∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) :
    comparisonBareLimitGap (.range (w++[(eta,c)]) E) (.range (v++[(eta,d)]) F) profile N := by
  intro word zeta mass A hEq hl Q hQc hQ x hx
  have hEta := (outer_unique w word eta zeta c mass E A hEq).1
  subst zeta
  have hCut : encodedLimitPairCertificateTail (rawNoteEncode eta.1) (positiveExprEncode Q) c d≤N := by
    rw [hQc]
    exact (equal_profile_bounds q w v eta c d E F hq profile hprofile).1.trans hN
  have hScalar := LimitPairCertificate.actual_program.2 eta hl Q hQ c d
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)
    (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)
    ((hCut.trans hx).trans (inner_growth v eta d F hS x))
    ((hCut.trans hx).trans (inner_growth w eta c E hR x))
  have hStrict := hWin x hx
  rw [SourceKernelCalls.shape_semantics.2.2 w eta c E x,SourceKernelCalls.shape_semantics.2.2 v eta d F x] at hStrict ⊢
  have hGap := hScalar.2.2.2 hStrict
  exact (actualFixedLimitProfileMonotone _ Q hQ (Nat.le_add_right _ _)).trans_lt hGap

theorem equal_right_gap (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F)))
    (profile N : Nat) (hprofile : profile∈[q.2.1,q.2.2,1]) (hN : encodedRangeRangeLocalTail q≤N)
    (hWin : ∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x<
      actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) x) :
    comparisonBareLimitGap (.range (v++[(eta,d)]) F) (.range (w++[(eta,c)]) E) profile N := by
  intro word zeta mass A hEq hl Q hQc hQ x hx
  have hEta := (outer_unique v word eta zeta d mass F A hEq).1
  subst zeta
  have hCut : encodedLimitPairCertificateTail (rawNoteEncode eta.1) (positiveExprEncode Q) d c≤N := by
    rw [hQc]
    exact (equal_profile_bounds q w v eta c d E F hq profile hprofile).2.1.trans hN
  have hScalar := LimitPairCertificate.actual_program.2 eta hl Q hQ d c
    (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)
    ((hCut.trans hx).trans (inner_growth w eta c E hR x))
    ((hCut.trans hx).trans (inner_growth v eta d F hS x))
  have hStrict := hWin x hx
  rw [SourceKernelCalls.shape_semantics.2.2 w eta c E x,SourceKernelCalls.shape_semantics.2.2 v eta d F x] at hStrict ⊢
  have hGap := hScalar.2.2.2 hStrict
  exact (actualFixedLimitProfileMonotone _ Q hQ (Nat.le_add_right _ _)).trans_lt hGap

end LogicLineages.OrdinalComparison.RangeRangeNode
