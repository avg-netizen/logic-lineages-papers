module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

theorem dual_realization : Targets.groupInfinitaryDualRealization.{u} := by
  classical
  intro G _ n φ
  induction φ with
  | qf q =>
    intro a
    rfl
  | disjEx s m matrix ih =>
    intro a
    simp only [Formula.dual, Formula.Realize, ih, not_exists]
  | conjAll s m matrix ih =>
    intro a
    simp only [Formula.dual, Formula.Realize, ih, not_forall]

theorem dual_complexity : Targets.groupInfinitaryDualComplexity.{v} := by
  intro side α n φ h
  induction h with
  | qf side q =>
    cases side <;> exact Complexity.qf _ (.neg q)
  | sigma positive s m matrix β lower rank ih =>
    exact Complexity.pi positive s m (fun i => (matrix i).dual) β lower ih
  | pi positive s m matrix β lower rank ih =>
    exact Complexity.sigma positive s m (fun i => (matrix i).dual) β lower ih

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
