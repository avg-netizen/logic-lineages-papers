module
public import LogicLineages.OrdinalComparison.PrincipalKernelWordTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPrincipalKernelWordPositions : Targets.ActualPrincipalKernelWordPositions := by
  intro es
  induction es with
  | nil => intro c; simp [principalKernelWord]
  | cons e es ih =>
    intro c
    have hm : ((e :: es).zipIdx.map fun p =>
        (p.1, c + principalBlocksWeight ((e :: es).take p.2))) =
        (e, c) :: (es.zipIdx.map fun p =>
          (p.1, (c + (1 + Vendor.R1.treeWeight e)) + principalBlocksWeight (es.take p.2))) := by
      rw [List.zipIdx_cons', List.map_cons, List.map_map]
      simp only [List.take_zero, principalBlocksWeight, List.map_nil, List.sum_nil, Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro p _
      rcases p with ⟨f, i⟩
      simp [Function.comp_def, principalBlocksWeight, Nat.add_assoc]
    rw [hm, List.reverse_cons]
    exact congrArg (fun w => w ++ [(e, c)]) (ih (c + (1 + Vendor.R1.treeWeight e)))

theorem actualPrincipalKernelWordAppend : Targets.ActualPrincipalKernelWordAppend := by
  intro es
  induction es with
  | nil => intro fs c; simp [principalKernelWord, principalBlocksWeight]
  | cons e es ih =>
    intro fs c
    simp only [List.cons_append, principalKernelWord, ih, principalBlocksWeight,
      List.map_cons, List.sum_cons, Nat.add_assoc, List.append_assoc]

end LogicLineages.OrdinalComparison
