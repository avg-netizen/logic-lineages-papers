module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonAssembly

def GoodLayers : List (List ComparisonQuery) → Prop
  | [] => True
  | layer::rest =>
    (∀ q∈layer,∀ child∈encodedComparisonQueryChildren q,child∈rest.headD []) ∧ GoodLayers rest

theorem good_of_index (layers : List (List ComparisonQuery))
    (h : ∀ k : Nat,k<layers.length →
      encodedComparisonQueryFrontierStep (layers.getD k [])=layers.getD (k+1) []) : GoodLayers layers := by
  induction layers with
  | nil => trivial
  | cons layer rest ih =>
    refine ⟨?_,ih ?_⟩
    · intro q hq child hc
      have hm : child∈encodedComparisonQueryFrontierStep layer := List.mem_flatMap.mpr ⟨q,hq,hc⟩
      have he := h 0 (by simp)
      simp only [List.getD_cons_zero,List.getD_cons_succ] at he
      rw [he] at hm
      cases rest <;> exact hm
    · intro k hk
      have he := h (k+1) (by simp only [List.length_cons]; omega)
      simpa only [List.getD_cons_succ] using he

theorem actual_layers_good (q : ComparisonQuery) : GoodLayers (encodedComparisonQueryLayers q) := by
  apply good_of_index
  intro k hk
  have hlen := (ComparisonQuery.layers_program.2 q).1
  have hlast := (ComparisonQuery.layers_program.2 q).2.2.1
  have hsteps := (ComparisonQuery.layers_program.2 q).2.2.2
  by_cases hlt : k<encodedComparisonTreeDepth q.1
  · exact (hsteps k hlt).symm
  · have heq : k=encodedComparisonTreeDepth q.1 := by omega
    subst k
    rw [hlast]
    have hout : (encodedComparisonQueryLayers q).getD (encodedComparisonTreeDepth q.1+1) []=[] := by
      apply List.getD_eq_default
      omega
    rw [hout]
    rfl

theorem table_correct (layers : List (List ComparisonQuery)) (hgood : GoodLayers layers) :
    (∀ record∈encodedComparisonQueryTable layers,actualComparisonQueryCorrect record.1 record.2) ∧
    (∀ q∈layers.headD [],∃ result : ComparisonNodeResult,(q,result)∈encodedComparisonQueryTable layers) := by
  induction layers with
  | nil =>
    constructor
    · intro record hm
      cases hm
    · intro q hm
      cases hm
  | cons layer rest ih =>
    have hi := ih hgood.2
    have hcover : ∀ q∈layer,comparisonQueryTableCovers q (encodedComparisonQueryTable rest) := by
      intro q hq child hc
      obtain ⟨result,hm⟩ := hi.2 child (hgood.1 q hq child hc)
      exact ⟨result,hm,hi.1 _ hm⟩
    constructor
    · intro record hm
      change record∈layer.map (fun q => (q,encodedComparisonQueryNode q (encodedComparisonQueryTable rest)))++
        encodedComparisonQueryTable rest at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨q,hq,heq⟩ := List.mem_map.mp hm
        subst record
        exact node_correct q _ (hcover q hq)
      · exact hi.1 record hm
    · intro q hq
      refine ⟨encodedComparisonQueryNode q (encodedComparisonQueryTable rest),?_⟩
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨q,hq,rfl⟩

theorem result_correct : Targets.ActualComparisonQueryResultCorrect := by
  intro q
  have hAll := (table_correct (encodedComparisonQueryLayers q) (actual_layers_good q)).1
  have hfirst := (ComparisonQuery.layers_program.2 q).2.1
  cases hLayers : encodedComparisonQueryLayers q with
  | nil =>
    rw [hLayers] at hfirst
    simp only [List.getD_nil] at hfirst
    cases hfirst
  | cons layer rest =>
    rw [hLayers] at hfirst
    simp only [List.getD_cons_zero] at hfirst
    have hmem : (q,encodedComparisonQueryResult q)∈encodedComparisonQueryTable (encodedComparisonQueryLayers q) := by
      simp only [encodedComparisonQueryResult,hLayers,hfirst,encodedComparisonQueryTable,List.foldr_cons,
        encodedComparisonQueryLayer,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.headD_cons]
      exact List.mem_cons_self
    exact hAll _ hmem

theorem full : Targets.FullActualComparisonQueryAssembly :=
  ⟨node_program,node_correct,assembly_programs,result_correct⟩

end LogicLineages.OrdinalComparison.ComparisonAssembly
