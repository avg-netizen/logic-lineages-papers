module
public import LogicLineages.OrdinalComparison.SourceKernelCallsTargets
public import LogicLineages.OrdinalComparison.SourcePeakCallsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceKernelCalls

private theorem inner_shape (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) :
    comparisonLiteralSourceHeadCount (comparisonLiteralInner w E)=comparisonPositiveSourceHeadCount E ∧
      comparisonAuxiliarySourceWord (comparisonLiteralInner w E)=w := by
  cases w <;> exact ⟨rfl,rfl⟩

private theorem word_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordRun (v++w) t=
      ((actualPrincipalWordRun w (actualPrincipalWordRun v t).1).1,
        (actualPrincipalWordRun v t).2+(actualPrincipalWordRun w (actualPrincipalWordRun v t).1).2) := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨e,c⟩
    simp [actualPrincipalWordRun,ih,Nat.add_assoc]

theorem shape_semantics : Targets.ActualOuterStripShapeSemantics := by
  refine ⟨inner_shape,?_,?_⟩
  · intro w eta c E hv
    cases w with
    | nil => exact hv.2.2.1
    | cons p w =>
      refine ⟨by simp,?_,hv.2.2⟩
      intro q hq
      exact hv.2.1 q (List.mem_append_left _ hq)
  · intro w eta c E x
    change (actualPrincipalWordRun _ (actualFixedLimitProfileEval E x)).1=_
    rw [show comparisonRawWord (w++[(eta,c)])=comparisonRawWord w++[(eta.1,c)] by
      simp [comparisonRawWord]]
    rw [word_append]
    cases w <;> rfl

theorem program : Targets.ActualOuterStripProgram := by
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hw : Primrec (fun n : Nat => ((Encodable.decode (α := List (Nat × Nat))
      (n/2).unpair.1).getD []).reverse.tail.reverse) :=
    Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp hp)) (Primrec.const []))))
  have hc := Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp hp)
  have hr := Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.encode.comp hw) (Primrec.snd.comp hp)))
  refine ⟨Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) Primrec.id
    (Primrec.ite (Primrec.eq.comp hw (Primrec.const [])) hc hr),?_⟩
  intro w eta c E
  let word := encodePrincipalKernelWord (comparisonRawWord (w++[(eta,c)]))
  let q := Nat.pair (Encodable.encode word) (positiveExprEncode E)
  have hm0 : (2*q+1)%2=1 := by omega
  have hd : (2*q+1)/2=q := by omega
  change (if (2*q+1)%2=0 then 2*q+1 else
    let p := ((2*q+1)/2).unpair
    let inner := ((Encodable.decode (α := List (Nat × Nat)) p.1).getD []).reverse.tail.reverse
    if inner=[] then 2*p.2 else 2*Nat.pair (Encodable.encode inner) p.2+1)=_
  rw [hm0,if_neg (by decide),hd]
  simp only [q,Nat.unpair_pair,Encodable.encodek,Option.getD_some]
  simp only [word,encodePrincipalKernelWord,comparisonRawWord,List.map_append,List.map_singleton,
    List.reverse_append,List.reverse_singleton,List.singleton_append,List.tail_cons,List.reverse_reverse]
  cases w <;> rfl

private theorem strip_left (budget : Nat) (eta : NONote)
    (hbound : Vendor.R1.treeWeight eta.1≤budget) (w : List (NONote × Nat))
    (c : Nat) (E : FixedLimitPositiveExpr) (F : OneVariableComparisonExpr) :
    comparisonLiteralPairStep budget (comparisonLiteralInner w E,F) (.range (w++[(eta,c)]) E,F) := by
  apply Or.inr
  refine ⟨?_,w.map Prod.fst,(comparisonAuxiliarySourceWord F).map Prod.fst,[],eta,hbound,?_,?_,?_⟩
  · change comparisonLiteralSourceHeadCount (comparisonLiteralInner w E)+comparisonLiteralSourceHeadCount F=
      comparisonPositiveSourceHeadCount E+comparisonLiteralSourceHeadCount F
    rw [(inner_shape w E).1]
  · intro sigma hs; cases hs
  · simp only [comparisonLiteralPairMeasure,comparisonAuxiliarySourceWord,List.map_append,List.map_cons,
      List.map_nil,List.append_assoc,List.singleton_append]
    exact List.Perm.refl _
  · simp only [comparisonLiteralPairMeasure,(inner_shape w E).2,List.map_append,List.append_nil]
    exact List.Perm.refl _

theorem mixed_child : Targets.ActualMixedLimitChildCall := by
  intro budget eta hbound X v d F
  apply Or.inr
  refine ⟨?_,(comparisonAuxiliarySourceWord X).map Prod.fst++v.map Prod.fst,[],[],eta,hbound,?_,?_,?_⟩
  · change comparisonLiteralSourceHeadCount X+comparisonLiteralSourceHeadCount (comparisonLiteralInner v F)=
      comparisonLiteralSourceHeadCount X+comparisonPositiveSourceHeadCount F
    rw [(inner_shape v F).1]
  · intro sigma hs; cases hs
  · simp only [comparisonLiteralPairMeasure,comparisonAuxiliarySourceWord,List.map_append,List.map_cons,
      List.map_nil,List.append_assoc,List.singleton_append]
    exact List.Perm.refl _
  · simp only [comparisonLiteralPairMeasure,(inner_shape v F).2,List.map_append,List.append_nil]
    exact List.Perm.refl _

theorem transitive_wellFounded : Targets.LiteralPairTransitiveStepWellFounded :=
  fun budget => (SourcePeakCalls.wellFounded budget).transGen

theorem equal_child : Targets.ActualEqualOuterChildCall := by
  intro budget eta hbound w v c d E F
  exact Relation.TransGen.tail
    (Relation.TransGen.single (mixed_child budget eta hbound (comparisonLiteralInner w E) v d F))
    (strip_left budget eta hbound w c E (.range (v++[(eta,d)]) F))

theorem full : Targets.FullActualOuterKernelChildCalls :=
  ⟨program,shape_semantics,transitive_wellFounded,equal_child,mixed_child⟩

end LogicLineages.OrdinalComparison.SourceKernelCalls
