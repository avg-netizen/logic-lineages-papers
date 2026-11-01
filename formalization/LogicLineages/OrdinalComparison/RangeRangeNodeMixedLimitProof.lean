module
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedSetupProof
public import LogicLineages.OrdinalComparison.KernelProfileLeafProof
public import LogicLineages.OrdinalComparison.ProfileCompositionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

private theorem genuine_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordGenuine (v++w) t ↔
      actualPrincipalWordGenuine v t ∧ actualPrincipalWordGenuine w (actualPrincipalWordRun v t).1 := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordGenuine,actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨e,c⟩
    simp [actualPrincipalWordGenuine,actualPrincipalWordRun,ih,and_assoc]

theorem last_kernel_domain (v : List (NONote × Nat)) (lower : NONote) (d : Nat)
    (F : FixedLimitPositiveExpr) (x : Nat)
    (hd : oneVariableComparisonDomainAt (.range (v++[(lower,d)]) F) x) :
    d+actualOrdinalNorm (Ordinal.omega0^lower.1.repr)≤
      actualOneVariableComparisonValue (comparisonLiteralInner v F) x := by
  have hraw : comparisonRawWord (v++[(lower,d)])=comparisonRawWord v++[(lower.1,d)] := by
    simp [comparisonRawWord]
  change actualPrincipalWordGenuine (comparisonRawWord (v++[(lower,d)])) (actualFixedLimitProfileEval F x) at hd
  rw [hraw] at hd
  have hh := ((genuine_append _ _ _).mp hd).2.1
  have hi : actualOneVariableComparisonValue (comparisonLiteralInner v F) x=
      (actualPrincipalWordRun (comparisonRawWord v) (actualFixedLimitProfileEval F x)).1 := by
    cases v <;> rfl
  simpa only [hi] using hh

theorem lower_context_below (eta lower : NONote) (hp : 0<lower.1.repr)
    (hlt : lower.1.repr<eta.1.repr) :
    fixedLimitProfileBelow (Ordinal.omega0^eta.1.repr) (.head (comparisonPrincipalNote lower) .input) := by
  refine ⟨?_,?_,True.intro⟩
  · rw [(LimitPairCertificate.principal_source.2 lower).1]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  · rw [(LimitPairCertificate.principal_source.2 lower).1]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hlt

/-- Literal higher-limit child certificate with the lower-head context.
The request is one of the actual finite query requests, never an oracle. -/
theorem mixed_context_gap (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr)
    (hchild : (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (hctx : positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (x : Nat) (hx : encodedComparisonTableTail table≤x)
    (hWin : actualOneVariableComparisonValue (comparisonLiteralInner v F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) :
    actualProfileHead (comparisonPrincipalNote lower)
      (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)<
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x := by
  have hp : 0<lower.1.repr := hS.2.1 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  have hrequest := ((ComparisonQuery.coverage.2 q).2.1 _ (List.mem_append_right _ hctx)).1
  obtain ⟨result,hm,hcorrect⟩ := child_record q table hc (.range (w++[(eta,c)]) E)
    (comparisonLiteralInner v F) hchild _ hrequest
  have hN := (ComparisonNode.table_member_tail table _ result hm).trans hx
  have hd := hcorrect _ _ rfl rfl hR (SourceKernelCalls.shape_semantics.2.1 v lower d F hS)
  have hSig : result.1=2 := (hd.1.2.2 x hN).2.2.2.2.mpr hWin
  exact hd.2.1 hSig w eta c E rfl hl (.head (comparisonPrincipalNote lower) .input) rfl
    (lower_context_below eta lower hp hlt) x hN

/-- At every genuine point, comparing the higher limit value to the lower
inner value decides its comparison with the entire lower kernel. -/
theorem mixed_limit_point (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr)
    (hchild : (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (hctx : positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (x : Nat) (hx : encodedComparisonTableTail table≤x)
    (hd : oneVariableComparisonDomainAt (.range (v++[(lower,d)]) F) x) :
    (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x≤
        actualOneVariableComparisonValue (comparisonLiteralInner v F) x ↔
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x<
        actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x) ∧
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) x<
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x ↔
      actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) := by
  have hp : 0<lower.1.repr := hS.2.1 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  have hdom := last_kernel_domain v lower d F x hd
  have hSmall := kernel_strict lower hp d _ hdom
  have hLarge := kernel_below_head lower hp d _ hdom
  have hA : actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x≤
      actualOneVariableComparisonValue (comparisonLiteralInner v F) x →
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x<
        actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x := by
    intro h
    rw [SourceKernelCalls.shape_semantics.2.2 v lower d F x]
    exact h.trans_lt hSmall
  have hB : actualOneVariableComparisonValue (comparisonLiteralInner v F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x →
      actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x := by
    intro h
    rw [SourceKernelCalls.shape_semantics.2.2 v lower d F x]
    exact hLarge.trans_lt (mixed_context_gap q w v eta lower c d E F hR hS hl hlt hchild hctx table hc x hx h)
  exact ⟨⟨hA,fun h => by by_contra hn; exact (lt_asymm h) (hB (Nat.lt_of_not_ge hn))⟩,
    ⟨hB,fun h => by by_contra hn; exact (lt_asymm h) (hA (Nat.le_of_not_gt hn))⟩⟩

theorem mixed_limit_sign_stable (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr)
    (hchild : (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (hctx : positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (N : Nat) (hDom : oneVariableComparisonDomainBound (.range (v++[(lower,d)]) F)≤N)
    (x y : Nat) (hxT : encodedComparisonTableTail table≤x) (hyT : encodedComparisonTableTail table≤y)
    (hx : N≤x) (hy : N≤y) :
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x)
      (actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x)=
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) y)
      (actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) y) := by
  obtain ⟨result,hm,hcorrect⟩ := child_record q table hc (.range (w++[(eta,c)]) E)
    (comparisonLiteralInner v F) hchild (1,1) (ComparisonQuery.coverage.2 q).1
  have hd := (hcorrect _ _ rfl rfl hR (SourceKernelCalls.shape_semantics.2.1 v lower d F hS)).1
  have hN := ComparisonNode.table_member_tail table _ result hm
  have hInput := ComparisonNode.weak_order_stable _ _ result hd x y (hN.trans hxT) (hN.trans hyT)
  have hX := mixed_limit_point q w v eta lower c d E F hR hS hl hlt hchild hctx table hc x hxT
    ((OneVariableComparison.source_program.2.2 _ hS).2.2 x (hDom.trans hx)).1
  have hY := mixed_limit_point q w v eta lower c d E F hR hS hl hlt hchild hctx table hc y hyT
    ((OneVariableComparison.source_program.2.2 _ hS).2.2 y (hDom.trans hy)).1
  have hLt := hX.1.symm.trans (hInput.trans hY.1)
  have hGt : actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x ↔
    actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) y<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) y := by
    rw [←hX.2,←hY.2]
    omega
  unfold comparisonNaturalSign
  simp only [hLt,hGt]

end LogicLineages.OrdinalComparison.RangeRangeNode
