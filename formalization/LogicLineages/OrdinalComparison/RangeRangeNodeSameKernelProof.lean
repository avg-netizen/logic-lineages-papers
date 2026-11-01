module
public import LogicLineages.OrdinalComparison.RangeRangeNodeQueryProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem same_kernel_sign_stable (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hchild : (oneVariableComparisonEncode (comparisonLiteralInner w E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2)
    (N : Nat) (hMass : encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c d≤N)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (x y : Nat) (hxT : encodedComparisonTableTail table≤x) (hyT : encodedComparisonTableTail table≤y)
    (hx : N≤x) (hy : N≤y) :
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x)
      (actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) x)=
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) y)
      (actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) y) := by
  obtain ⟨result,hm,hcorrect⟩ := child_record q table hc (comparisonLiteralInner w E) (comparisonLiteralInner v F)
    hchild (1,1) (ComparisonQuery.coverage.2 q).1
  have hData := (hcorrect _ _ rfl rfl (SourceKernelCalls.shape_semantics.2.1 w eta c E hR)
    (SourceKernelCalls.shape_semantics.2.1 v eta d F hS)).1
  have hChildN := ComparisonNode.table_member_tail table _ result hm
  have hInputStable := sign_data_stable _ _ result hData x y (hChildN.trans hxT) (hChildN.trans hyT)
  have hEta : 0<eta.1.repr := hR.2.1 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  have hMassX := hMass.trans hx
  have hMassY := hMass.trans hy
  have hX := KernelInputProgram.actual_program.2 eta hEta c d
    (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)
    (hMassX.trans (inner_growth w eta c E hR x)) (hMassX.trans (inner_growth v eta d F hS x))
  have hY := KernelInputProgram.actual_program.2 eta hEta c d
    (actualOneVariableComparisonValue (comparisonLiteralInner w E) y)
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) y)
    (hMassY.trans (inner_growth w eta c E hR y)) (hMassY.trans (inner_growth v eta d F hS y))
  have hKey := input_classifier_stable (rawNoteEncode eta.1) c d _ _ _ _ hInputStable
  have hLt : actualSuffixKernel (Ordinal.omega0^eta.1.repr) c
      (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) d
        (actualOneVariableComparisonValue (comparisonLiteralInner v F) x) ↔
    actualSuffixKernel (Ordinal.omega0^eta.1.repr) c
      (actualOneVariableComparisonValue (comparisonLiteralInner w E) y)<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) d
        (actualOneVariableComparisonValue (comparisonLiteralInner v F) y) := by
    rw [←hX.2.2.1,←hY.2.2.1,hKey]
  have hGt : actualSuffixKernel (Ordinal.omega0^eta.1.repr) d
      (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c
        (actualOneVariableComparisonValue (comparisonLiteralInner w E) x) ↔
    actualSuffixKernel (Ordinal.omega0^eta.1.repr) d
      (actualOneVariableComparisonValue (comparisonLiteralInner v F) y)<
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c
        (actualOneVariableComparisonValue (comparisonLiteralInner w E) y) := by
    rw [←hX.2.2.2.2,←hY.2.2.2.2,hKey]
  rw [SourceKernelCalls.shape_semantics.2.2 w eta c E x,SourceKernelCalls.shape_semantics.2.2 v eta d F x,
    SourceKernelCalls.shape_semantics.2.2 w eta c E y,SourceKernelCalls.shape_semantics.2.2 v eta d F y]
  unfold comparisonNaturalSign
  simp only [hLt,hGt]

/-- The exact same-limit winning gap, with its actual numerical programme bound
made explicit so that a mixed normalizer can pay it from the original pool. -/
theorem same_kernel_gap (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (profile N : Nat)
    (hCut : encodedLimitPairCertificateTail (rawNoteEncode eta.1) profile c d≤N)
    (hWin : ∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) x<
      actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) :
    comparisonBareLimitGap (.range (w++[(eta,c)]) E) (.range (v++[(eta,d)]) F) profile N := by
  intro word zeta mass A hEq hl Q hQc hQ x hx
  have hEta := (outer_unique w word eta zeta c mass E A hEq).1
  subst zeta
  have hTail : encodedLimitPairCertificateTail (rawNoteEncode eta.1) (positiveExprEncode Q) c d≤N := by
    rw [hQc]
    exact hCut
  have hScalar := LimitPairCertificate.actual_program.2 eta hl Q hQ c d
    (actualOneVariableComparisonValue (comparisonLiteralInner v F) x)
    (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)
    ((hTail.trans hx).trans (inner_growth v eta d F hS x))
    ((hTail.trans hx).trans (inner_growth w eta c E hR x))
  have hStrict := hWin x hx
  rw [SourceKernelCalls.shape_semantics.2.2 w eta c E x,SourceKernelCalls.shape_semantics.2.2 v eta d F x] at hStrict ⊢
  have hGap := hScalar.2.2.2 hStrict
  exact (actualFixedLimitProfileMonotone _ Q hQ (Nat.le_add_right _ _)).trans_lt hGap

end LogicLineages.OrdinalComparison.RangeRangeNode
