module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Proof

theorem flatMap_congr {A B:Type} (xs:List A) (f g:A→List B)
    (h:∀a∈xs,f a=g a):xs.flatMap f=xs.flatMap g:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.flatMap_cons,h a List.mem_cons_self,
      ih (fun b hb=>h b (List.mem_cons_of_mem a hb))]

theorem atomInput_ext (k:Nat) (a:AtomData) (f g:Nat→Nat)
    (h:∀j<k,f j=g j):atomInput k a f=atomInput k a g:=by
  unfold atomInput
  apply congrArg (fun n=>rawNormCode a.2.1+a.2.2.1+n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.mp hj)]

theorem valueAt_ext (k:Nat) (E:UpperData) (f g:Nat→Nat)
    (h:∀j<k,f j=g j):valueAt k E f=valueAt k E g:=by
  unfold valueAt
  apply congrArg₂ Nat.add
  · apply congrArg (fun n=>E.1+n)
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    rw [h j (List.mem_range.mp hj)]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [atomInput_ext k a f g h]

theorem variablesAt_ext (k:Nat) (E:UpperData) (f g:Nat→List Nat)
    (h:∀j<k,f j=g j):variablesAt k E f=variablesAt k E g:=by
  unfold variablesAt
  apply congrArg₂ List.append
  · apply flatMap_congr
    intro j hj
    rw [h j (List.mem_range.mp hj)]
  · apply flatMap_congr
    intro a ha
    exact flatMap_congr (List.range k) f g (fun j hj=>h j (List.mem_range.mp hj))

private theorem child_answer (k:Nat) (Γ:List Nat) (C E:Nat) (table:Table) (j:Nat) (hj:j<k):
    (((children (k::Γ,C,E,table)).map joint).getD j (0,[]))=
      joint (Γ,(certificateData C).1,(certificateData C).2.getD j 0,table):=by
  rw [List.getD_eq_getElem _ (0,[]) (by simp only [children,List.length_map,List.length_range];exact hj)]
  simp only [children,List.getElem_map,List.getElem_range]

theorem finiteCallEquation:Targets.FiniteCallEquation:=by
  constructor
  · intro p q hq
    rcases p with ⟨Γ,C,E,table⟩
    cases Γ with
    | nil=>simp [children] at hq
    | cons k Γ=>
      obtain ⟨j,hj,hq⟩:=List.mem_map.mp hq
      subst q
      simp only [List.length_cons]
      omega
  · intro p
    rcases p with ⟨Γ,C,E,table⟩
    cases Γ with
    | nil=>rfl
    | cons k Γ=>
      apply Prod.ext
      · exact valueAt_ext k (upperData E) _ _ (fun j hj=>
          (congrArg Prod.fst (child_answer k Γ C E table j hj)).symm)
      · exact variablesAt_ext k (upperData E) _ _ (fun j hj=>
          (congrArg Prod.snd (child_answer k Γ C E table j hj)).symm)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Proof
