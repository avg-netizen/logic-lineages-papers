module
public import LogicLineages.OrdinalComparison.WholeScheduledCountTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.WholeScheduledCount.Proof

theorem exactRecursion : Targets.ExactRecursion := by
  intro budget a ha
  constructor
  · intro hf
    conv_lhs => rw [count, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_pos hf]
  · intro hn
    conv_lhs => rw [count, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_neg (not_lt_of_ge hn)]
    rfl

theorem firstFinite : Targets.FirstFinite := by
  intro budget a
  induction a using Ordinal.lt_wf.induction generalizing budget with
  | h a ih =>
    intro ha
    by_cases hf : a < Ordinal.omega0
    · have hc := (exactRecursion budget a ha).1 hf
      rw [hc]
      refine ⟨hf, ?_⟩
      intro i hi
      have hz : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact ⟨ha, le_rfl, fun h => False.elim (Nat.not_lt_zero 0 h)⟩
    · have hn := le_of_not_gt hf
      have hd := (actualMaximumPredecessor_correct a (Ordinal.omega0_pos.trans_le hn) ha (budget 0)).1.1
      have hi := ih (actualMaximumPredecessor a (budget 0)) hd
        (fun i => budget (i + 1)) (hd.trans ha)
      have hc := (exactRecursion budget a ha).2 hn
      rw [hc]
      constructor
      · exact hi.1
      · intro i hib
        cases i with
        | zero => exact ⟨ha, le_rfl, fun _ => hn⟩
        | succ i =>
          have hii := hi.2 i (Nat.le_of_succ_le_succ hib)
          exact ⟨hii.1, hii.2.1.trans hd.le,
            fun hit => hii.2.2 (Nat.lt_of_succ_lt_succ hit)⟩


end LogicLineages.OrdinalComparison.WholeScheduledCount.Proof
