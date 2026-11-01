module
public import LogicLineages.OrdinalComparison.ComparisonExpansionPeakImageProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionEncodingProof
public import LogicLineages.OrdinalComparison.SourceSuccessorCallsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion

theorem word_source (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) :
    encodedComparisonWord (oneVariableComparisonEncode (.range w E))=
      encodePrincipalKernelWord (comparisonRawWord w) := by
  let q := Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w))) (positiveExprEncode E)
  have hd : (2*q+1)/2=q := by omega
  change (Encodable.decode (α := List (Nat × Nat)) ((2*q+1)/2).unpair.1).getD []=_
  rw [hd]
  simp only [q,Nat.unpair_pair,Encodable.encodek,Option.getD_some]

theorem outer_source (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr) :
    encodedComparisonOuter (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))=(rawNoteEncode eta.1,c) := by
  simp [encodedComparisonOuter,word_source,encodePrincipalKernelWord,comparisonRawWord,List.map_append]

private theorem swap_parent_step (budget : Nat) (G H E F : OneVariableComparisonExpr)
    (h : comparisonLiteralPairStep budget (G,H) (E,F)) : comparisonLiteralPairStep budget (G,H) (F,E) := by
  have hh : (comparisonLiteralPairMeasure F E).heads=(comparisonLiteralPairMeasure E F).heads :=
    Nat.add_comm _ _
  have hp : (comparisonLiteralPairMeasure F E).exponents.Perm (comparisonLiteralPairMeasure E F).exponents :=
    (List.perm_append_comm (l₁ := comparisonAuxiliarySourceWord F) (l₂ := comparisonAuxiliarySourceWord E)).map Prod.fst
  rcases h with hhead | ⟨hhead,before,after,added,eta,hEta,hadded,hcurrent,hnext⟩
  · apply Or.inl
    change (comparisonLiteralPairMeasure G H).heads<(comparisonLiteralPairMeasure F E).heads
    rw [hh]
    exact hhead
  · exact Or.inr ⟨hhead.trans hh.symm,before,after,added,eta,hEta,hadded,hp.trans hcurrent,hnext⟩

theorem swap_parent_trans (budget : Nat) (G H E F : OneVariableComparisonExpr)
    (h : Relation.TransGen (comparisonLiteralPairStep budget) (G,H) (E,F)) :
    Relation.TransGen (comparisonLiteralPairStep budget) (G,H) (F,E) := by
  cases h with
  | single h => exact .single (swap_parent_step budget G H E F h)
  | tail h hlast => exact .tail h (swap_parent_step budget _ _ E F hlast)

theorem swap_parent_image {budget : Nat} {E F : OneVariableComparisonExpr} {p : Nat × Nat}
    (h : ActualChildImage budget E F p) : ActualChildImage budget F E p := by
  obtain ⟨G,H,hG,hH,hGV,hHV,hGB,hHB,hstep⟩ := h
  exact ⟨G,H,hG,hH,hGV,hHV,hGB,hHB,swap_parent_trans budget G H E F hstep⟩

theorem equal_image (budget : Nat) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hE : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hF : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hEB : comparisonSourceBounded budget (.range (w++[(eta,c)]) E))
    (hFB : comparisonSourceBounded budget (.range (v++[(eta,d)]) F)) :
    ActualChildImage budget (.range (w++[(eta,c)]) E) (.range (v++[(eta,d)]) F)
      (encodedComparisonStripOuter (oneVariableComparisonEncode (.range (w++[(eta,c)]) E)),
        encodedComparisonStripOuter (oneVariableComparisonEncode (.range (v++[(eta,d)]) F))) := by
  have hEta : Vendor.R1.treeWeight eta.1≤budget := hEB.2 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  exact ⟨comparisonLiteralInner w E,comparisonLiteralInner v F,
    (SourceKernelCalls.program.2 w eta c E).symm,(SourceKernelCalls.program.2 v eta d F).symm,
    SourceKernelCalls.shape_semantics.2.1 w eta c E hE,SourceKernelCalls.shape_semantics.2.1 v eta d F hF,
    SourceCarrierClosure.stripped budget w eta c E hEB,SourceCarrierClosure.stripped budget v eta d F hFB,
    SourceKernelCalls.equal_child budget eta hEta w v c d E F⟩

theorem mixed_image (budget : Nat) (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hE : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hF : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hEB : comparisonSourceBounded budget (.range (w++[(eta,c)]) E))
    (hFB : comparisonSourceBounded budget (.range (v++[(lower,d)]) F))
    (hLt : lower.1.repr<eta.1.repr) (p : Nat × Nat)
    (hp : p∈encodedComparisonMixedChildren (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
      (oneVariableComparisonEncode (.range (v++[(lower,d)]) F))) :
    ActualChildImage budget (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F) p := by
  have hEta : Vendor.R1.treeWeight eta.1≤budget := hEB.2 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  have hLower : Vendor.R1.treeWeight lower.1≤budget := hFB.2 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  have hPos : 0<lower.1.repr := hF.2.1 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨added,last,hsource,hcode,hvalid,hlo,hhi,hweight,hstop,hadded,hN,heval⟩ :=
    SuccessorNormalization.actual_program.2 w E eta lower c hE hPos hLt
  have hNB : comparisonSourceBounded budget (.range ((w++added)++[(last,c)]) E) := by
    obtain ⟨addedB,lastB,hsourceB,hBound⟩ := SourceCarrierClosure.normalized budget w E eta lower c hE hEB hPos hLt
    have hsame : OneVariableComparisonExpr.range ((w++addedB)++[(lastB,c)]) E=
        .range ((w++added)++[(last,c)]) E := source_injective (hsourceB.symm.trans hsource)
    rw [hsame] at hBound
    exact hBound
  dsimp only [encodedComparisonMixedChildren] at hp
  rw [outer_source w eta c E,outer_source v lower d F,prefix_program.2 w eta c E] at hp
  rw [hsource,hcode] at hp
  by_cases heq : rawNoteEncode last.1=rawNoteEncode lower.1
  · have hpval : p=(encodedComparisonStripOuter (oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E)),
        encodedComparisonStripOuter (oneVariableComparisonEncode (.range (v++[(lower,d)]) F))) := by
      simpa only [if_pos heq,List.mem_singleton] using hp
    subst p
    refine ⟨comparisonLiteralInner (w++added) E,comparisonLiteralInner v F,
      (SourceKernelCalls.program.2 (w++added) last c E).symm,(SourceKernelCalls.program.2 v lower d F).symm,
      SourceKernelCalls.shape_semantics.2.1 (w++added) last c E hvalid,
      SourceKernelCalls.shape_semantics.2.1 v lower d F hF,
      SourceCarrierClosure.stripped budget (w++added) last c E hNB,
      SourceCarrierClosure.stripped budget v lower d F hFB,?_⟩
    exact SourceSuccessorCalls.replacement budget eta lower hEta hLower w v added c d E F
      (fun q hq => ⟨(hadded q hq).1,((hadded q hq).2).trans hEta⟩)
  · have hpval : p=(oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E),
        encodedComparisonStripOuter (oneVariableComparisonEncode (.range (v++[(lower,d)]) F))) := by
      simpa only [if_neg heq,List.mem_singleton] using hp
    subst p
    have hlast : lower.1.repr<last.1.repr := by
      apply lt_of_le_of_ne hlo
      intro hrep
      have heqNote : lower=last := Subtype.ext (ONote.repr_inj.mp hrep)
      exact heq (congrArg (fun z : NONote => rawNoteEncode z.1) heqNote.symm)
    have hnew : ∀ q∈added++[(last,c)],lower.1.repr<q.1.1.repr ∧ Vendor.R1.treeWeight q.1.1≤budget := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact ⟨(hadded q hq).1,((hadded q hq).2).trans hEta⟩
      · have heq : q=(last,c) := List.mem_singleton.mp hq
        subst q
        exact ⟨hlast,hweight.trans hEta⟩
    have hcall := SourceSuccessorCalls.replacement budget eta lower hEta hLower w v (added++[(last,c)]) c d E F hnew
    have hinner : comparisonLiteralInner (w++(added++[(last,c)])) E=
        .range ((w++added)++[(last,c)]) E := by
      rw [←List.append_assoc]
      generalize w++added=word
      cases word <;> rfl
    rw [hinner] at hcall
    exact ⟨.range ((w++added)++[(last,c)]) E,comparisonLiteralInner v F,rfl,
      (SourceKernelCalls.program.2 v lower d F).symm,hvalid,
      SourceKernelCalls.shape_semantics.2.1 v lower d F hF,hNB,
      SourceCarrierClosure.stripped budget v lower d F hFB,hcall⟩

end LogicLineages.OrdinalComparison.ComparisonExpansion
