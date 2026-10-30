module

public import LogicLineages.ModelsAlgebra.PGroups.LimitRootsTargets
public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimit

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem limit_annihilation : Targets.groupLimitAnnihilation.{u} := by
  intro G _ f c h z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (iterationTransition f) z
  change c • limitStage f i x = 0
  simpa only [map_nsmul, map_zero] using congrArg (limitStage f i) (h x)

theorem limit_socle_roots : Targets.groupLimitSocleRoots.{u} := by
  intro G _ f hf p c h z hz
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (iterationTransition f) z
  change p • limitStage f i x = 0 at hz
  have hx : p • x = 0 := by
    apply limit_stage_injective G f hf i
    simpa only [map_nsmul, map_zero] using hz
  obtain ⟨y, hy⟩ := h x hx
  refine ⟨limitStage f (i + 1) y, ?_⟩
  change c • limitStage f (i + 1) y = limitStage f i x
  rw [← map_nsmul, hy]
  have ht : iterationTransition f i (i + 1) (Nat.le_succ i) x = f x := by
    change (f : G → G)^[i + 1 - i] x = f x
    simp
  simpa only [ht] using limit_stage_compatibility G f i (i + 1) (Nat.le_succ i) x

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
