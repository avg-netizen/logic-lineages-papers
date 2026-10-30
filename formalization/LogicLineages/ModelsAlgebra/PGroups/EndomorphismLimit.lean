module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimitTargets

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

theorem limit_stage_injective : Targets.groupLimitStageInjective.{u} := by
  intro G _ f hf i
  exact DirectLimit.mk_injective (iterationTransition f)
    (fun i j hij => iteration_transition_injective G f hf i j hij) i

theorem limit_stage_compatibility : Targets.groupLimitStageCompatibility.{u} := by
  intro G _ f i j hij x
  exact DirectLimit.mk_apply (f := iterationTransition f) i j x hij

theorem limit_ranges_monotone : Targets.groupLimitRangesMonotone.{u} := by
  intro G _ f i j hij x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨iterationTransition f i j hij y, limit_stage_compatibility G f i j hij y⟩

theorem limit_range_cover : Targets.groupLimitRangeCover.{u} := by
  intro G _ f z
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (iterationTransition f) z
  exact ⟨i, x, rfl⟩

theorem endomorphism_limit_countable : Targets.groupEndomorphismLimitCountable.{u} := by
  intro G _ _ f
  let q : (Σ _ : ℕ, G) → EndomorphismLimit f := fun z => ⟦z⟧
  have hq : Function.Surjective q := Quotient.mk_surjective
  exact hq.countable

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
