module

public import LogicLineages.ModelsAlgebra.PGroups.LimitPiTwoTargets
public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismLimit
public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem endomorphism_limit_pi_two : Targets.groupEndomorphismLimitPiTwo.{u,v} := by
  intro G _ f hf φ hφ htruth
  apply increasing_pi_two_preservation (EndomorphismLimit f) (fun i => (limitStage f i).range)
    (limit_ranges_monotone G f) (limit_range_cover G f) φ hφ
  intro i
  let e : G ≃+ (limitStage f i).range :=
    AddMonoidHom.ofInjective (limit_stage_injective G f hf i)
  have he : (fun j : Fin 0 => e (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → (limitStage f i).range) := by
    funext j
    exact Fin.elim0 j
  have hc := GroupBackAndForth.comparison_isomorphism 2 G (limitStage f i).range e 0 Fin.elim0
  have ht := (truth_transfer 2 G (limitStage f i).range 0 Fin.elim0 _ hc).1 φ hφ htruth
  simpa only [he] using ht

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
