module
public import LogicLineages.OrdinalComparison.ComparisonTreeDepthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree

private theorem layers_get (root : Nat × Nat) (k : Nat) (hk : k≤encodedComparisonTreeDepth root) :
    (encodedComparisonTreeLayers root).getD k []=encodedComparisonFrontier root k := by
  unfold encodedComparisonTreeLayers
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map,List.length_range]; omega)]
  simp only [List.getElem_map,List.getElem_range]

theorem layers_program : Targets.ActualComparisonTreeLayersProgram := by
  have hmap : Primrec (fun p : (Nat × Nat) × Nat =>
      (List.range (p.2+1)).map (encodedComparisonFrontier p.1)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (frontier_program.2.1.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine ⟨hmap.to_comp.comp (Computable.id.pair depth_computable),?_⟩
  intro root
  refine ⟨?_,?_,?_,?_⟩
  · simp only [encodedComparisonTreeLayers,List.length_map,List.length_range]
  · rw [layers_get root 0 (Nat.zero_le _)]
    rfl
  · rw [layers_get root _ le_rfl]
    exact depth_closed root
  · intro k hk
    rw [layers_get root (k+1) (by omega),layers_get root k (by omega)]
    exact (frontier_program.2.2 root).2 k

theorem full : Targets.FullActualFiniteComparisonTree :=
  ⟨wellFounded,frontier_program,terminates,depth_program,layers_program⟩

end LogicLineages.OrdinalComparison.ComparisonTree
