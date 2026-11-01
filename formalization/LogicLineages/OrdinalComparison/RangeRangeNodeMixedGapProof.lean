module
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedLimitProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem mixed_high_gap (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr)
    (hchild : (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (hctx : positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (profile N : Nat) (hprofile : profile∈[q.2.1,q.2.2])
    (hNT : encodedComparisonTableTail table≤N)
    (hDom : oneVariableComparisonDomainBound (.range (v++[(lower,d)]) F)≤N)
    (hWin : ∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) :
    comparisonBareLimitGap (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F) profile N := by
  intro word zeta mass A hEq hz Q hQc hQ x hx
  have hEta := (outer_unique w word eta zeta c mass E A hEq).1
  subst zeta
  have hp : 0<lower.1.repr := hS.2.1 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  have hContext := lower_context_below eta lower hp hlt
  have hreq := ((ComparisonQuery.coverage.2 q).2.2 profile hprofile
    (positiveExprEncode (.head (comparisonPrincipalNote lower) .input)) hctx).1
  have hcode : encodedProfileCompose profile (positiveExprEncode (.head (comparisonPrincipalNote lower) .input))=
      positiveExprEncode (fixedProfileCompose Q (.head (comparisonPrincipalNote lower) .input)) := by
    rw [←hQc]
    exact ProfileComposition.program.2 Q _
  rw [hcode] at hreq
  obtain ⟨result,hm,hcorrect⟩ := child_record q table hc (.range (w++[(eta,c)]) E)
    (comparisonLiteralInner v F) hchild _ hreq
  have hN := (ComparisonNode.table_member_tail table _ result hm).trans (hNT.trans hx)
  have hd := hcorrect _ _ rfl rfl hR (SourceKernelCalls.shape_semantics.2.1 v lower d F hS)
  have hDomX := ((OneVariableComparison.source_program.2.2 _ hS).2.2 x (hDom.trans hx)).1
  have hKernelDom := last_kernel_domain v lower d F x hDomX
  have hInner : actualOneVariableComparisonValue (comparisonLiteralInner v F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x := by
    have hh := kernel_strict lower hp d _ hKernelDom
    have hw := hWin x hx
    rw [SourceKernelCalls.shape_semantics.2.2 v lower d F x] at hw
    exact hh.trans hw
  have hSig : result.1=2 := (hd.1.2.2 x hN).2.2.2.2.mpr hInner
  have hGap := hd.2.1 hSig w eta c E rfl hl
    (fixedProfileCompose Q (.head (comparisonPrincipalNote lower) .input)) rfl
    (ProfileComposition.source _ Q _ hQ hContext).1 x hN
  rw [(ProfileComposition.source _ Q _ hQ hContext).2 _] at hGap
  have hBound : actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x≤
      actualProfileHead (comparisonPrincipalNote lower)
        (actualOneVariableComparisonValue (comparisonLiteralInner v F) x) := by
    rw [SourceKernelCalls.shape_semantics.2.2 v lower d F x]
    exact kernel_below_head lower hp d _ hKernelDom
  exact (actualFixedLimitProfileMonotone _ Q hQ hBound).trans_lt hGap

theorem mixed_low_gap (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr)
    (hchild : (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (hctx : positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (profile N : Nat) (hNT : encodedComparisonTableTail table≤N)
    (hDom : oneVariableComparisonDomainBound (.range (v++[(lower,d)]) F)≤N)
    (hCut : encodedKernelProfileLeafTail (encodedComparisonPrincipalNote (rawNoteEncode lower.1)) profile d≤N)
    (hWin : ∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x<
      actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x) :
    comparisonBareLimitGap (.range (v++[(lower,d)]) F) (.range (w++[(eta,c)]) E) profile N := by
  intro word zeta mass A hEq hz Q hQc hQ x hx
  have hEta := (outer_unique v word lower zeta d mass F A hEq).1
  subst zeta
  have hL := (LimitPairCertificate.principal_source.2 lower).1
  have hBelow : fixedLimitProfileBelow (comparisonPrincipalNote lower).1.repr Q := by
    rw [hL]
    exact hQ
  have hLarge : Ordinal.omega0<(comparisonPrincipalNote lower).1.repr := by
    rw [hL]
    simpa only [Ordinal.opow_one] using
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.one_lt_of_isSuccLimit hz))
  have hTail : encodedKernelProfileLeafTail (rawNoteEncode (comparisonPrincipalNote lower).1)
      (positiveExprEncode Q) d≤actualOneVariableComparisonValue (comparisonLiteralInner v F) x := by
    rw [hQc,←(LimitPairCertificate.principal_source.2 lower).2]
    exact (hCut.trans hx).trans (inner_growth v lower d F hS x)
  have hScalar := (KernelProfileLeaf.bounded_program.2 (comparisonPrincipalNote lower)
    ⟨lower.1.repr,hL⟩ hLarge Q hBelow d _ hTail).2
  have hClass := mixed_limit_point q w v eta lower c d E F hR hS hl hlt hchild hctx table hc x (hNT.trans hx)
    ((OneVariableComparison.source_program.2.2 _ hS).2.2 x (hDom.trans hx)).1
  have hInner := hClass.1.mpr (hWin x hx)
  have hGap := hScalar _ hInner
  rw [hL] at hGap
  rw [SourceKernelCalls.shape_semantics.2.2 v lower d F x]
  exact hGap

theorem gap_transfer_loser (G E F : OneVariableComparisonExpr) (profile N : Nat)
    (hval : ∀ x : Nat,N≤x → actualOneVariableComparisonValue E x=actualOneVariableComparisonValue F x)
    (hgap : comparisonBareLimitGap G E profile N) : comparisonBareLimitGap G F profile N := by
  intro w eta c A hEq hl Q hQc hQ x hx
  rw [←hval x hx]
  exact hgap w eta c A hEq hl Q hQc hQ x hx

end LogicLineages.OrdinalComparison.RangeRangeNode
