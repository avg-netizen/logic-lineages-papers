module
public import LogicLineages.OrdinalComparison.ComparisonQueryProgramProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionKernelImageProof
public import LogicLineages.OrdinalComparison.ComparisonTreeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonQuery

private theorem profile_requested (q : ComparisonQuery) (p : Nat)
    (hp : p∈encodedComparisonQueryProfiles q) :
    (p,1)∈encodedComparisonQueryRequests q ∧ (1,p)∈encodedComparisonQueryRequests q := by
  constructor
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,by simp⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,by simp⟩)

theorem coverage : Targets.ActualComparisonQueryRequestCoverage := by
  constructor
  · intro w eta c E
    simp only [encodedComparisonHeadContext,ComparisonExpansion.outer_source,
      (LimitPairCertificate.principal_source.2 eta).2,positiveExprEncode]
  · intro q
    refine ⟨List.mem_append_left _ (List.mem_singleton_self _),?_,?_⟩
    · intro p hp
      apply profile_requested q p
      have hh : p∈([1,q.2.1,q.2.2]++encodedComparisonQueryContexts q.1)++
          [q.2.1,q.2.2].flatMap (fun p => (encodedComparisonQueryContexts q.1).map (encodedProfileCompose p)) :=
        List.mem_append_left _ hp
      simpa only [encodedComparisonQueryProfiles,List.append_assoc] using hh
    · intro p hp context hc
      apply profile_requested q (encodedProfileCompose p context)
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨context,hc,rfl⟩⟩)

theorem child_projection : Targets.ActualComparisonQueryChildProjection := by
  intro q next
  constructor
  · intro hn
    obtain ⟨source,hs,hm⟩ := List.mem_flatMap.mp hn
    obtain ⟨profiles,hp,heq⟩ := List.mem_map.mp hm
    cases heq
    exact ⟨hs,hp⟩
  · rintro ⟨hs,hp⟩
    exact List.mem_flatMap.mpr ⟨next.1,hs,List.mem_map.mpr ⟨next.2,hp,Prod.mk.eta⟩⟩

private theorem query_frontier_succ (q : ComparisonQuery) (n : Nat) :
    encodedComparisonQueryFrontier q (n+1)=
      encodedComparisonQueryFrontierStep (encodedComparisonQueryFrontier q n) :=
  Function.iterate_succ_apply' _ _ _

theorem frontier_projection : Targets.ActualComparisonQueryFrontierProjection := by
  intro q depth
  induction depth with
  | zero =>
    intro next hn
    have heq : next=q := List.mem_singleton.mp hn
    subst next
    exact List.mem_singleton_self _
  | succ n ih =>
    intro next hn
    rw [query_frontier_succ] at hn
    obtain ⟨parent,hparent,hchild⟩ := List.mem_flatMap.mp hn
    have hs := (child_projection parent next).mp hchild
    rw [(ComparisonTree.frontier_program.2.2 q.1).2 n]
    exact List.mem_flatMap.mpr ⟨parent.1,ih parent hparent,hs.1⟩

private theorem query_closed (q : ComparisonQuery) :
    encodedComparisonQueryFrontier q (encodedComparisonTreeDepth q.1)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro next hn
  have h := frontier_projection q (encodedComparisonTreeDepth q.1) next hn
  rw [ComparisonTree.depth_closed q.1] at h
  cases h

private theorem layers_get (q : ComparisonQuery) (k : Nat) (hk : k≤encodedComparisonTreeDepth q.1) :
    (encodedComparisonQueryLayers q).getD k []=encodedComparisonQueryFrontier q k := by
  unfold encodedComparisonQueryLayers
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map,List.length_range]; omega)]
  simp only [List.getElem_map,List.getElem_range]

attribute [local irreducible] encodedComparisonTreeDepth encodedComparisonQueryFrontier

theorem layers_program : Targets.ActualComparisonQueryLayersProgram := by
  have hmap : Primrec (fun p : ComparisonQuery × Nat =>
      (List.range (p.2+1)).map (encodedComparisonQueryFrontier p.1)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (frontier_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine ⟨hmap.to_comp.comp (Computable.id.pair (ComparisonTree.depth_computable.comp Computable.fst)),?_⟩
  intro q
  refine ⟨?_,?_,?_,?_⟩
  · simp only [encodedComparisonQueryLayers,List.length_map,List.length_range]
  · rw [layers_get q 0 (Nat.zero_le _)]
    unfold encodedComparisonQueryFrontier
    rfl
  · rw [layers_get q _ le_rfl]
    exact query_closed q
  · intro k hk
    rw [layers_get q (k+1) (by omega),layers_get q k (by omega)]
    exact query_frontier_succ q k

theorem full : Targets.FullActualFiniteComparisonQueryTree :=
  ⟨program,coverage,child_projection,frontier_projection,layers_program⟩

end LogicLineages.OrdinalComparison.ComparisonQuery
