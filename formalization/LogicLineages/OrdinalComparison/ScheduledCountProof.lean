module
public import LogicLineages.OrdinalComparison.ScheduledCountTargets
public import LogicLineages.OrdinalComparison.ControlledCountProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualScheduledCountRecursion : Targets.ActualScheduledCountRecursion := by
  intro budget a ha
  constructor
  · intro hf
    conv_lhs => rw [actualScheduledCount, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_pos hf]
  · intro hn
    conv_lhs => rw [actualScheduledCount, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_neg (not_lt_of_ge hn)]
    rfl

theorem actualScheduledStateLastStep : Targets.ActualScheduledStateLastStep := by
  intro budget a i
  induction i generalizing budget a with
  | zero => rfl
  | succ i ih =>
    exact ih (fun j => budget (j + 1)) (actualControlledStep (fun _ => budget 0) a)

theorem actualScheduledFirstFinite : Targets.ActualScheduledFirstFinite := by
  intro budget a
  induction a using Ordinal.lt_wf.induction generalizing budget with
  | h a ih =>
    intro ha
    by_cases hf : a < Ordinal.omega0
    · have hc := (actualScheduledCountRecursion budget a ha).1 hf
      rw [hc]
      refine ⟨hf, ?_⟩
      intro i hi
      have hz : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact ⟨ha, le_rfl, fun h => False.elim (Nat.not_lt_zero 0 h)⟩
    · have hn := le_of_not_gt hf
      have hd := actualControlledStepStrict (fun _ => budget 0) a hn ha
      have hi := ih (actualControlledStep (fun _ => budget 0) a) hd
        (fun i => budget (i + 1)) (hd.trans ha)
      have hc := (actualScheduledCountRecursion budget a ha).2 hn
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

theorem actualScheduledConstantCount : Targets.ActualScheduledConstantCount := by
  intro b a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha
    by_cases hf : a < Ordinal.omega0
    · rw [(actualScheduledCountRecursion (fun _ => b) a ha).1 hf,
        (actualControlledCountRecursion (fun _ => b) a ha).1 hf]
    · have hn := le_of_not_gt hf
      have hd := actualControlledStepStrict (fun _ => b) a hn ha
      rw [(actualScheduledCountRecursion (fun _ => b) a ha).2 hn,
        (actualControlledCountRecursion (fun _ => b) a ha).2 hn]
      exact congrArg (fun n : Nat => n + 1) (ih _ hd (hd.trans ha))

end LogicLineages.OrdinalComparison
