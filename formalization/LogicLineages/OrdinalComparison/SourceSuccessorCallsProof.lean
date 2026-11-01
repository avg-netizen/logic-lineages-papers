module
public import LogicLineages.OrdinalComparison.SourceSuccessorCallsTargets
public import LogicLineages.OrdinalComparison.SourceKernelCallsProof
public import LogicLineages.OrdinalComparison.SuccessorNormalizationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceSuccessorCalls

private theorem strip_left (budget : Nat) (eta : NONote)
    (hbound : Vendor.R1.treeWeight eta.1≤budget) (w : List (NONote × Nat))
    (c : Nat) (E : FixedLimitPositiveExpr) (F : OneVariableComparisonExpr) :
    comparisonLiteralPairStep budget (comparisonLiteralInner w E,F) (.range (w++[(eta,c)]) E,F) := by
  apply Or.inr
  refine ⟨?_,w.map Prod.fst,(comparisonAuxiliarySourceWord F).map Prod.fst,[],eta,hbound,?_,?_,?_⟩
  · change comparisonLiteralSourceHeadCount (comparisonLiteralInner w E)+comparisonLiteralSourceHeadCount F=
      comparisonPositiveSourceHeadCount E+comparisonLiteralSourceHeadCount F
    rw [(SourceKernelCalls.shape_semantics.1 w E).1]
  · intro sigma hs; cases hs
  · simp only [comparisonLiteralPairMeasure,comparisonAuxiliarySourceWord,List.map_append,List.map_cons,
      List.map_nil,List.append_assoc,List.singleton_append]
    exact List.Perm.refl _
  · simp only [comparisonLiteralPairMeasure,(SourceKernelCalls.shape_semantics.1 w E).2,List.map_append,List.append_nil]
    exact List.Perm.refl _

private theorem replace_lower (budget : Nat) (lower : NONote)
    (hbound : Vendor.R1.treeWeight lower.1≤budget) (w v added : List (NONote × Nat))
    (d : Nat) (E F : FixedLimitPositiveExpr)
    (hadded : ∀ p∈added,lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤budget) :
    comparisonLiteralPairStep budget
      (comparisonLiteralInner (w++added) E,comparisonLiteralInner v F)
      (comparisonLiteralInner w E,.range (v++[(lower,d)]) F) := by
  apply Or.inr
  refine ⟨?_,w.map Prod.fst,v.map Prod.fst,added.map Prod.fst,lower,hbound,?_,?_,?_⟩
  · change comparisonLiteralSourceHeadCount (comparisonLiteralInner (w++added) E)+
      comparisonLiteralSourceHeadCount (comparisonLiteralInner v F)=
        comparisonLiteralSourceHeadCount (comparisonLiteralInner w E)+comparisonPositiveSourceHeadCount F
    rw [(SourceKernelCalls.shape_semantics.1 (w++added) E).1,
      (SourceKernelCalls.shape_semantics.1 v F).1,(SourceKernelCalls.shape_semantics.1 w E).1]
  · intro sigma hs
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
    exact ⟨(hadded p hp).2,(hadded p hp).1⟩
  · change ((comparisonAuxiliarySourceWord (comparisonLiteralInner w E)++(v++[(lower,d)])).map Prod.fst).Perm
        (w.map Prod.fst++lower::v.map Prod.fst)
    rw [List.map_append,(SourceKernelCalls.shape_semantics.1 w E).2]
    simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using
        List.Perm.append_left (w.map Prod.fst)
          (List.perm_append_comm (l₁ := v.map Prod.fst) (l₂ := [lower]))
  · simp only [comparisonLiteralPairMeasure,(SourceKernelCalls.shape_semantics.1 (w++added) E).2,
      (SourceKernelCalls.shape_semantics.1 v F).2,List.map_append,List.append_assoc]
    exact List.Perm.refl _

theorem replacement : Targets.ActualBoundedHigherReplacementChild := by
  intro budget eta lower hEta hLower w v added c d E F hadded
  exact Relation.TransGen.tail
    (Relation.TransGen.single (replace_lower budget lower hLower w v added d E F hadded))
    (strip_left budget eta hEta w c E (.range (v++[(lower,d)]) F))

theorem computed : Targets.ActualComputedSuccessorChildCalls := by
  intro budget w v E F eta lower c d hv hEta hLower hPos hLt
  obtain ⟨added,last,hsource,hcode,hvalid,hlo,hhi,hweight,hstop,hadded,hN,heval⟩ :=
    SuccessorNormalization.actual_program.2 w E eta lower c hv hPos hLt
  refine ⟨added,last,hsource,hcode,hvalid,hlo,hstop,?_,?_⟩
  · intro _
    exact replacement budget eta lower hEta hLower w v added c d E F
      (fun p hp => ⟨(hadded p hp).1,((hadded p hp).2).trans hEta⟩)
  · intro hlast
    have hnew : ∀ p∈added++[(last,c)],lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤budget := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨(hadded p hp).1,((hadded p hp).2).trans hEta⟩
      · have heq : p=(last,c) := List.mem_singleton.mp hp
        subst p
        exact ⟨hlast,hweight.trans hEta⟩
    have hr := replacement budget eta lower hEta hLower w v (added++[(last,c)]) c d E F hnew
    have hinner : comparisonLiteralInner (w++(added++[(last,c)])) E=
        .range ((w++added)++[(last,c)]) E := by
      rw [←List.append_assoc]
      generalize w++added=word
      cases word <;> rfl
    rw [hinner] at hr
    exact hr

theorem full : Targets.FullActualCombinedSuccessorChildCalls := ⟨replacement,computed⟩

end LogicLineages.OrdinalComparison.SourceSuccessorCalls
