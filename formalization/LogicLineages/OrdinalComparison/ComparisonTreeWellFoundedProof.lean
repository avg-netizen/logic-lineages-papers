module
public import LogicLineages.OrdinalComparison.ComparisonTreeTargets
public import LogicLineages.OrdinalComparison.ComparisonExpansionImageProof
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainImageProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree

private theorem source_accessible (budget : Nat) (E F : OneVariableComparisonExpr)
    (hE : oneVariableComparisonValid E) (hF : oneVariableComparisonValid F)
    (hEB : comparisonSourceBounded budget E) (hFB : comparisonSourceBounded budget F) :
    Acc ComparisonNumericChild (oneVariableComparisonEncode E,oneVariableComparisonEncode F) := by
  have h : ∀ pair : OneVariableComparisonExpr × OneVariableComparisonExpr,
      oneVariableComparisonValid pair.1 → oneVariableComparisonValid pair.2 →
      comparisonSourceBounded budget pair.1 → comparisonSourceBounded budget pair.2 →
      Acc ComparisonNumericChild (oneVariableComparisonEncode pair.1,oneVariableComparisonEncode pair.2) := by
    intro pair
    refine (SourceKernelCalls.transitive_wellFounded budget).induction
      (C := fun pair : OneVariableComparisonExpr × OneVariableComparisonExpr =>
        oneVariableComparisonValid pair.1 → oneVariableComparisonValid pair.2 →
        comparisonSourceBounded budget pair.1 → comparisonSourceBounded budget pair.2 →
        Acc ComparisonNumericChild (oneVariableComparisonEncode pair.1,oneVariableComparisonEncode pair.2)) pair ?_
    intro pair ih hE hF hEB hFB
    refine Acc.intro _ ?_
    intro child hchild
    obtain ⟨G,H,hG,hH,hGV,hHV,hGB,hHB,hstep⟩ :=
      ComparisonExpansion.image budget pair.1 pair.2 hE hF hEB hFB child hchild
    have hs := ih (G,H) hstep hGV hHV hGB hHB
    simpa only [hG,hH] using hs
  exact h (E,F) hE hF hEB hFB

theorem wellFounded : Targets.ActualNumericComparisonChildWellFounded := by
  refine ⟨fun root => ?_⟩
  by_cases hE : encodedComparisonSourceDomain root.1=1
  · by_cases hF : encodedComparisonSourceDomain root.2=1
    · obtain ⟨E,hEc,hEV⟩ := (ComparisonSourceDomain.image root.1).mp hE
      obtain ⟨F,hFc,hFV⟩ := (ComparisonSourceDomain.image root.2).mp hF
      have hB := SourceCarrierClosure.initial E F hEV hFV
      have hAcc := source_accessible
        (encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F))
          E F hEV hFV hB.1 hB.2
      simpa only [hEc,hFc,Prod.mk.eta] using hAcc
    · refine Acc.intro root ?_
      intro child hc
      have hbad : encodedComparisonSourceDomain root.1≠1 ∨ encodedComparisonSourceDomain root.2≠1 := Or.inr hF
      simpa only [ComparisonNumericChild,encodedComparisonChildren,if_pos hbad,List.not_mem_nil] using hc
  · refine Acc.intro root ?_
    intro child hc
    have hbad : encodedComparisonSourceDomain root.1≠1 ∨ encodedComparisonSourceDomain root.2≠1 := Or.inl hE
    simpa only [ComparisonNumericChild,encodedComparisonChildren,if_pos hbad,List.not_mem_nil] using hc

end LogicLineages.OrdinalComparison.ComparisonTree
