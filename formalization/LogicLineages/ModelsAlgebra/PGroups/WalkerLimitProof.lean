module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeProof
public import Mathlib.Data.Countable.Defs
public import Mathlib.Logic.Encodable.Pi
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_limit_faithful : Targets.walkerLimitFaithful := by
  intro p hp parent n
  exact DirectLimit.mk_injective (walkerStageMap p parent)
    (fun i j h => walker_stage_faithful p hp parent i j h) n

theorem walker_limit_compatible : Targets.walkerLimitCompatible := by
  intro p parent n m h
  ext x
  exact DirectLimit.mk_apply (f := walkerStageMap p parent) n m x h

theorem walker_limit_digits : Targets.walkerLimitDigits := by
  intro p hp parent x
  obtain ⟨n, y, rfl⟩ := DirectLimit.exists_eq_mk (walkerStageMap p parent) x
  obtain ⟨d, hd⟩ := (walker_finite_tree_unique_digits p hp parent n).2 y
  exact ⟨n, d, congrArg (walkerStageInclusion p parent n) hd⟩

theorem walker_limit_countable : Targets.walkerLimitCountable := by
  intro p hp parent
  let F : (Σ n : ℕ, Fin n → Fin p) → WalkerSequentialGroup p parent :=
    fun d => walkerStageInclusion p parent d.1 (walkerFiniteDigitSum p parent d.1 d.2)
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨n, d, hd⟩ := walker_limit_digits p hp parent x
    exact ⟨⟨n, d⟩, hd⟩
  exact hF.countable

theorem walker_limit_generators : Targets.walkerLimitGenerators := by
  intro p parent n i
  have h : i.val + 1 ≤ n := i.isLt
  have hc := congrArg (fun f => f
      ((walkerFinitePresentation p parent (i.val+1)).generator (Fin.last i.val)))
    (walker_limit_compatible p parent (i.val+1) n h)
  change walkerStageInclusion p parent n
      (walkerStageMap p parent (i.val+1) n h
        ((walkerFinitePresentation p parent (i.val+1)).generator (Fin.last i.val))) =
      walkerSequentialGenerator p parent i.val at hc
  rw [walker_stage_generators] at hc
  exact hc

theorem walker_limit_relations : Targets.walkerLimitRelations := by
  intro p parent i
  have hh := congrArg (walkerStageInclusion p parent (i+1))
    (walker_finite_tree_relations p parent (i+1) (Fin.last i))
  rw [map_nsmul] at hh
  change p • walkerSequentialGenerator p parent i =
    walkerStageInclusion p parent (i+1) ((parent i).elim 0
      (fun j => (walkerFinitePresentation p parent (i+1)).generator j.castSucc)) at hh
  have ho (o : Option (Fin i)) : walkerStageInclusion p parent (i+1)
      (o.elim 0 (fun j => (walkerFinitePresentation p parent (i+1)).generator j.castSucc)) =
        o.elim 0 (fun j => walkerSequentialGenerator p parent j.val) := by
    cases o with
    | none => exact map_zero _
    | some j => exact walker_limit_generators p parent (i+1) j.castSucc
  exact hh.trans (ho (parent i))

end LogicLineages.ModelsAlgebra.PGroups
