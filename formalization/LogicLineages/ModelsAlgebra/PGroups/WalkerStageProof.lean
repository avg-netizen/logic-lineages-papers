module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerStageTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem stage_self (p : ℕ) (parent : WalkerParentSequence) (n : ℕ) :
    walkerStageMap p parent n n le_rfl = AddMonoidHom.id _ := by
  simp [walkerStageMap, Nat.leRecOn_self]

private theorem stage_succ (p : ℕ) (parent : WalkerParentSequence) (n m : ℕ) (h : n ≤ m) :
    walkerStageMap p parent n (m+1) (Nat.le_succ_of_le h) =
      (walkerStageStep p parent m).comp (walkerStageMap p parent n m h) := by
  simp [walkerStageMap, Nat.leRecOn_succ h]

theorem walker_stage_coherence : Targets.walkerStageCoherence := by
  intro p parent
  refine ⟨stage_self p parent, ?_⟩
  intro n m k hnm hmk
  induction k, hmk using Nat.le_induction with
  | base => simp [stage_self]
  | succ k hmk ih =>
    rw [stage_succ p parent m k hmk, stage_succ p parent n k (hnm.trans hmk)]
    rw [AddMonoidHom.comp_assoc, ih]

theorem walker_stage_faithful : Targets.walkerStageFaithful := by
  intro p hp parent n m h
  induction m, h using Nat.le_induction with
  | base => simpa [stage_self] using (Function.injective_id : Function.Injective
      (id : (walkerFinitePresentation p parent n).Carrier → _))
  | succ m h ih =>
    rw [stage_succ p parent n m h]
    intro x y hxy
    apply ih
    apply walker_adjunction_faithful (walkerFinitePresentation p parent m).Carrier p hp
      ((parent m).elim 0 (walkerFinitePresentation p parent m).generator)
    exact hxy

theorem walker_stage_generators : Targets.walkerStageGenerators := by
  intro p parent n m h i
  induction m, h using Nat.le_induction with
  | base => simp [stage_self]
  | succ m h ih =>
    rw [stage_succ p parent n m h, AddMonoidHom.comp_apply, ih]
    change walkerStageStep p parent m
      ((walkerFinitePresentation p parent m).generator (Fin.castLE h i)) =
        (walkerFinitePresentation p parent (m+1)).generator (Fin.castLE h i).castSucc
    simp only [walkerStageStep, walkerFinitePresentation, walkerFiniteExtension,
      Fin.lastCases_castSucc]
    rfl

end LogicLineages.ModelsAlgebra.PGroups
