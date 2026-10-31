module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthIsomorphismTargets
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth
universe u v

theorem back_forth_isomorphism : Targets.backForthIsomorphism.{u,v} := by
  intro α G H G' H' _ _ _ _ e f n a b
  have he : BackAndForth α (fun i => e (a i)) a := by
    simpa only [AddEquiv.symm_apply_apply] using comparison_isomorphism α G' G e.symm n (fun i => e (a i))
  have hf : BackAndForth α (fun i => f (b i)) b := by
    simpa only [AddEquiv.symm_apply_apply] using comparison_isomorphism α H' H f.symm n (fun i => f (b i))
  constructor
  · intro h
    exact comparison_transitive α G' H H' n _ _ _
      (comparison_transitive α G' G H n _ _ _ he h)
      (comparison_isomorphism α H H' f n b)
  · intro h
    exact comparison_transitive α G H' H n _ _ _
      (comparison_transitive α G G' H' n _ _ _ (comparison_isomorphism α G G' e n a) h) hf
end LogicLineages.ModelsAlgebra.PGroups
