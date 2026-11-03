module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonValueProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
open CommonLayerSyntax

private theorem children_variables (n code:Nat):codedVariables (n+1) code=
    (payload code).2.flatMap (fun a=>codedVariables n a.2):=by
  simp [codedVariables,decodeCommon,commonVariables,List.flatMap_map,Function.comp_def]

private theorem argument_support (n E F j i:Nat)
    (hi:i∈codedVariables n ((rowArguments E F).getD j (constantCode n 0))):
    i∈codedVariables (n+1) E++codedVariables (n+1) F:=by
  by_cases hj:j<(rowArguments E F).length
  · rw [List.getD_eq_getElem _ _ hj] at hi
    have ha:(rowArguments E F)[j]∈rowArguments E F:=List.getElem_mem hj
    have ha':(rowArguments E F)[j]∈
        (payload E).2.map Prod.snd++(payload F).2.map Prod.snd:=by
      simpa only [rowArguments,signedAtoms,List.map_append,List.map_map,Function.comp_def] using ha
    rw [children_variables,children_variables]
    rcases List.mem_append.mp ha' with he|hf
    · obtain ⟨a,ha,heq⟩:=List.mem_map.mp he
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨a,ha,by simpa only [heq] using hi⟩
    · obtain ⟨a,ha,heq⟩:=List.mem_map.mp hf
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨a,ha,by simpa only [heq] using hi⟩
  · rw [List.getD_eq_default _ _ (by omega),constant_variables] at hi
    cases hi

private theorem translated_support (n N:Nat) (args S:List Nat)
    (lower:Nat→Nat→Int→BaseFormula.Formula)
    (hl:∀A B d i,i∈(lower A B d).variables→i∈codedVariables n A++codedVariables n B)
    (ha:∀j i,i∈codedVariables n (args.getD j (constantCode n 0))→i∈S)
    (p:CommonHeadLargeGuards.Formula):
    ∀i∈(translateGuard lower n N args p).variables,i∈S:=by
  induction p with
  | truth=>simp [translateGuard,BaseFormula.Formula.variables]
  | falsity=>simp [translateGuard,BaseFormula.Formula.variables]
  | eq j k=>
    intro i hi
    rcases List.mem_append.mp (hl _ _ 0 i hi) with h|h
    · exact ha j i h
    · exact ha k i h
  | lt j k=>
    intro i hi
    rcases List.mem_append.mp (hl _ _ (-1) i hi) with h|h
    · exact ha j i h
    · exact ha k i h
  | bound c j=>
    intro i hi
    by_cases hc:c≤N
    · simp [translateGuard,hc,BaseFormula.Formula.variables] at hi
    · have hi':i∈(lower (args.getD j (constantCode n 0)) (constantCode n (c-N)) (-1)).variables:=by
        simpa only [translateGuard,if_neg hc,BaseFormula.Formula.variables] using hi
      rcases List.mem_append.mp (hl _ _ (-1) i hi') with h|h
      · exact ha j i h
      · rw [constant_variables] at h
        cases h
  | neg p ih=>exact ih
  | conj p q ihp ihq=>
    intro i hi
    rcases List.mem_append.mp hi with hp|hq
    · exact ihp i hp
    · exact ihq i hq
  | disj p q ihp ihq=>
    intro i hi
    rcases List.mem_append.mp hi with hp|hq
    · exact ihp i hp
    · exact ihq i hq

theorem originalSupport:Targets.OriginalRawSupport:=by
  intro Γ
  induction Γ with
  | nil=>
    intro E F desired i hi
    simp only [compile,baseCompare] at hi
    split_ifs at hi <;>
      simp_all [BaseFormula.Formula.variables,codedVariables,decodeCommon,commonVariables,List.mem_append]
    tauto
  | cons h Γ ih=>
    intro E F desired i hi
    exact translated_support Γ.length (rawNormCode h) (rowArguments E F)
      (codedVariables (Γ.length+1) E++codedVariables (Γ.length+1) F)
      (compile Γ) ih (fun j i hi=>argument_support Γ.length E F j i hi) _ i hi
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
