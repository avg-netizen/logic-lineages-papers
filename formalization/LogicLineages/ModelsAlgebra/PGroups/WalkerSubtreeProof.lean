module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSubtreeTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUniversalProof
public import Mathlib.Logic.Function.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem option_map_elim {α β γ : Type} (o : Option α) (f : α → β)
    (g : β → γ) (z : γ) : (o.map f).elim z g = o.elim z (fun x => g (f x)) := by
  cases o <;> rfl

private theorem generator_parent_node (p : ℕ) (parent : WalkerParentSequence) (n : ℕ)
    (i : Fin n) : p • (walkerFinitePresentation p parent n).generator i =
      (walkerParentNode parent n i).elim 0 (walkerFinitePresentation p parent n).generator := by
  simpa only [walkerParentNode, option_map_elim] using walker_finite_tree_relations p parent n i

theorem walker_finite_subtree_embedding : Targets.walkerFiniteSubtreeEmbedding := by
  classical
  intro p hp A B n m e he
  have hy : WalkerAssignmentRelations p A n
      (fun i => (walkerFinitePresentation p B m).generator (e i)) := by
    intro i
    rw [generator_parent_node, he i]
    simp only [walkerParentNode, option_map_elim]
  obtain ⟨f, hf, _⟩ := walker_finite_universal p hp A n
    (walkerFinitePresentation p B m).Carrier
    (fun i => (walkerFinitePresentation p B m).generator (e i)) hy
  refine ⟨f, ?_, hf⟩
  let z : Fin p := ⟨0, hp⟩
  let D (d : Fin n → Fin p) : Fin m → Fin p := Function.extend e d (fun _ => z)
  have hd (d : Fin n → Fin p) : f (walkerFiniteDigitSum p A n d) =
      walkerFiniteDigitSum p B m (D d) := by
    simp only [walkerFiniteDigitSum, map_sum, map_nsmul]
    refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
    · intro j hj
      dsimp only [D]
      rw [Function.extend_apply' _ _ _ hj]
      exact zero_nsmul _
    · intro i
      dsimp only [D]
      rw [e.injective.extend_apply]
      rw [hf i]
  intro x y hxy
  obtain ⟨d, rfl⟩ := (walker_finite_tree_unique_digits p hp A n).2 x
  obtain ⟨c, rfl⟩ := (walker_finite_tree_unique_digits p hp A n).2 y
  rw [hd d, hd c] at hxy
  have hD := (walker_finite_tree_unique_digits p hp B m).1 hxy
  apply congrArg (walkerFiniteDigitSum p A n)
  funext i
  have hi := congrFun hD (e i)
  simpa only [D, e.injective.extend_apply] using hi

end LogicLineages.ModelsAlgebra.PGroups
