module
public import LogicLineages.OrdinalComparison.RangeRangeNodeQueryProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem equal_sign_stable (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F)))
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (x y : Nat) (hxT : encodedComparisonTableTail table≤x) (hyT : encodedComparisonTableTail table≤y)
    (hx : encodedRangeRangeLocalTail q≤x) (hy : encodedRangeRangeLocalTail q≤y) :
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x)
      (actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) x)=
    comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) y)
      (actualOneVariableComparisonValue (.range (v++[(eta,d)]) F) y) := by
  obtain ⟨result,hm,hcorrect⟩ := child_record q table hc (comparisonLiteralInner w E) (comparisonLiteralInner v F)
    (equal_child_member q w v eta c d E F hR hS hq) (1,1) (ComparisonQuery.coverage.2 q).1
  have hData := (hcorrect _ _ rfl rfl (SourceKernelCalls.shape_semantics.2.1 w eta c E hR)
    (SourceKernelCalls.shape_semantics.2.1 v eta d F hS)).1
  have hChildN := ComparisonNode.table_member_tail table _ result hm
  have hInputStable := sign_data_stable _ _ result hData x y (hChildN.trans hxT) (hChildN.trans hyT)
  have hEta : 0<eta.1.repr := hR.2.1 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  have hMassX := (equal_mass_bound q w v eta c d E F hq).trans hx
  have hMassY := (equal_mass_bound q w v eta c d E F hq).trans hy
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

end LogicLineages.OrdinalComparison.RangeRangeNode
