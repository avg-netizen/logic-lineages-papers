module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralTargets
public import LogicLineages.ModelsAlgebra.PGroups.BackForth
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
universe u v

private theorem append_zero {G : Type u} {n : ℕ} (a : Fin n → G) (c : Fin 0 → G) :
    append a c = a := by
  funext i
  change Fin.addCases a c (Fin.castAdd 0 i) = a i
  exact Fin.addCases_left _

theorem back_forth_atomic : Targets.backForthAtomic.{u,v} := by
  intro α G H _ _ n a b hab
  by_cases hα : α = 0
  · subst α
    exact (zero_comparison G H n a b).mp hab
  · obtain ⟨c,hc⟩ := (positive_comparison α hα G H n a b).mp hab 0
      (lt_of_le_of_ne zero_le (Ne.symm hα)) 0 Fin.elim0
    have h := (zero_comparison H G (n+0) _ _).mp hc
    rw [append_zero,append_zero] at h
    exact fun s t => (h s t).symm

theorem back_forth_monotone : Targets.backForthMonotone.{u,v} := by
  intro α β hβα G H _ _ n a b hab
  by_cases hβ : β = 0
  · subst β
    exact (zero_comparison G H n a b).mpr (back_forth_atomic α G H n a b hab)
  · have hα : α ≠ 0 := ne_of_gt ((lt_of_le_of_ne zero_le (Ne.symm hβ)).trans_le hβα)
    apply (positive_comparison β hβ G H n a b).mpr
    intro γ hγ m d
    exact (positive_comparison α hα G H n a b).mp hab γ (hγ.trans_le hβα) m d

theorem back_forth_successor : Targets.backForthSuccessor.{u,v} := by
  intro α G H _ _ n a b
  have hpos : α+1 ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le : (0:Ordinal.{v}) ≤ α) (Order.lt_succ α))
  constructor
  · intro h m d
    exact (positive_comparison (α+1) hpos G H n a b).mp h α (Order.lt_succ α) m d
  · intro h
    apply (positive_comparison (α+1) hpos G H n a b).mpr
    intro β hβ m d
    obtain ⟨c,hc⟩ := h m d
    exact ⟨c,back_forth_monotone α β (Order.lt_add_one_iff.mp hβ) H G (n+m) _ _ hc⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
