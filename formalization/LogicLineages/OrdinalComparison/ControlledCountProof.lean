module
public import LogicLineages.OrdinalComparison.ControlledCountTargets
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualControlledCountRecursion : Targets.ActualControlledCountRecursion := by
  intro g a ha
  constructor
  · intro hf
    conv_lhs => rw [actualControlledCount, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_pos hf]
  · intro hn
    conv_lhs => rw [actualControlledCount, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_neg (not_lt_of_ge hn)]
    rfl

theorem actualControlledCountPhiAgreement : Targets.ActualControlledCountPhiAgreement := by
  intro a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha
    by_cases hf : a < Ordinal.omega0
    · have hc := (actualControlledCountRecursion Phi a ha).1 hf
      have ht := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).1 hf)
      change actualReplacementCount a = 0 at ht
      exact hc.trans ht.symm
    · have hn := le_of_not_gt hf
      have hd := actualControlledStepStrict Phi a hn ha
      have hi := ih (actualControlledStep Phi a) hd (hd.trans ha)
      have hc := (actualControlledCountRecursion Phi a ha).2 hn
      have ht := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).2 hn)
      change actualReplacementCount a = actualReplacementCount (actualDescentStep a) + 1 at ht
      rw [hc, hi]
      exact ht.symm

theorem actualControlledCountsJointMonotone : Targets.ActualControlledCountsJointMonotone := by
  intro g h hgh hmono a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro a' haa heps hnorm
    have ha := haa.trans_lt heps
    by_cases hf : a < Ordinal.omega0
    · rw [(actualControlledCountRecursion g a ha).1 hf]
      exact Nat.zero_le _
    · have hn := le_of_not_gt hf
      have hn' := hn.trans haa
      have hd := actualControlledStepStrict g a hn ha
      have hd' := actualControlledStepStrict h a' hn' heps
      have hj := actualControlledStepsJointMonotone g h hgh hmono a a' hn haa heps hnorm
      have hi := ih (actualControlledStep g a) hd (actualControlledStep h a') hj.1
        (hd'.trans heps) hj.2
      rw [(actualControlledCountRecursion g a ha).2 hn,
        (actualControlledCountRecursion h a' heps).2 hn']
      exact Nat.add_le_add_right hi 1

theorem actualOrderedControlsAndCounts : Targets.ActualOrderedControlsAndCounts := by
  intro g h _ hmono _ _ hgh
  exact actualControlledCountsJointMonotone g h hgh hmono

theorem fullActualOrderedControlsAndCounts : Targets.FullActualOrderedControlsAndCounts :=
  ⟨actualControlledCountRecursion, actualControlledCountPhiAgreement,
    actualControlledCountsJointMonotone, actualOrderedControlsAndCounts⟩

end LogicLineages.OrdinalComparison
