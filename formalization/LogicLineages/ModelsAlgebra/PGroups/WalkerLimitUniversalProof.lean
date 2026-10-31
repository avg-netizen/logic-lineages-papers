module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUniversalProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_limit_hom_ext : Targets.walkerLimitHomExt := by
  intro p hp parent K _ f g h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, d, rfl⟩ := walker_limit_digits p hp parent x
  simp only [walkerFiniteDigitSum, map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [walker_limit_generators p parent n i, h i.val]

theorem walker_limit_universal : Targets.walkerLimitUniversal := by
  classical
  intro p hp parent K _ y hy
  have hstage (n : ℕ) : WalkerAssignmentRelations p parent n (fun i => y i.val) := by
    intro i
    exact hy i.val
  let F (n : ℕ) : (walkerFinitePresentation p parent n).Carrier →+ K :=
    Classical.choose (walker_finite_universal p hp parent n K (fun i => y i.val) (hstage n))
  have hF (n : ℕ) (i : Fin n) : F n ((walkerFinitePresentation p parent n).generator i) = y i.val :=
    (Classical.choose_spec (walker_finite_universal p hp parent n K (fun i => y i.val) (hstage n))).1 i
  have compat (n m : ℕ) (h : n ≤ m) (x : (walkerFinitePresentation p parent n).Carrier) :
      F n x = F m (walkerStageMap p parent n m h x) := by
    obtain ⟨d, rfl⟩ := (walker_finite_tree_unique_digits p hp parent n).2 x
    simp only [walkerFiniteDigitSum, map_sum, map_nsmul, hF]
    apply Finset.sum_congr rfl
    intro i _
    rw [walker_stage_generators p parent n m h i, hF]
    rfl
  let f : WalkerSequentialGroup p parent →+ K :=
    { toFun := DirectLimit.lift (walkerStageMap p parent) (fun n => F n) compat
      map_zero' := DirectLimit.lift_zero (f := walkerStageMap p parent) F compat
      map_add' := DirectLimit.lift_add (f := walkerStageMap p parent) F compat }
  have hf (i : ℕ) : f (walkerSequentialGenerator p parent i) = y i := by
    change F (i+1) ((walkerFinitePresentation p parent (i+1)).generator (Fin.last i)) = y i
    exact hF (i+1) (Fin.last i)
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact walker_limit_hom_ext p hp parent K g f (fun i => (hg i).trans (hf i).symm)

end LogicLineages.ModelsAlgebra.PGroups
