module
public import LogicLineages.OrdinalComparison.PrefixTraceTargets
public import LogicLineages.OrdinalComparison.ControlledCountProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualControlledStateAfter_zero (g : Nat → Nat) (a : Ordinal) :
    actualControlledStateAfter g a 0 = a := rfl

theorem actualControlledStateAfter_succ (g : Nat → Nat) (a : Ordinal) (i : Nat) :
    actualControlledStateAfter g a (i + 1) = actualControlledStep g (actualControlledStateAfter g a i) :=
  Function.iterate_succ_apply' _ _ _

private theorem actualControlledStateAfter_succ_first (g : Nat → Nat) (a : Ordinal) (i : Nat) :
    actualControlledStateAfter g a (i + 1) = actualControlledStateAfter g (actualControlledStep g a) i :=
  Function.iterate_succ_apply _ _ _

theorem actualControlledTraceFirstFinite : Targets.ActualControlledTraceFirstFinite := by
  intro g a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
    intro ha
    by_cases hf : a < Ordinal.omega0
    · have hc := (actualControlledCountRecursion g a ha).1 hf
      rw [hc, actualControlledStateAfter_zero]
      refine ⟨hf, ?_⟩
      intro i hi
      have hz : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact ⟨ha, le_rfl, fun h => False.elim (Nat.not_lt_zero 0 h)⟩
    · have hn := le_of_not_gt hf
      have hd := actualControlledStepStrict g a hn ha
      have hi := ih (actualControlledStep g a) hd (hd.trans ha)
      have hc := (actualControlledCountRecursion g a ha).2 hn
      rw [hc]
      constructor
      · rw [actualControlledStateAfter_succ_first]
        exact hi.1
      · intro i hib
        cases i with
        | zero =>
          exact ⟨ha, le_rfl, fun _ => hn⟩
        | succ i =>
          rw [actualControlledStateAfter_succ_first]
          have hii := hi.2 i (Nat.le_of_succ_le_succ hib)
          exact ⟨hii.1, hii.2.1.trans hd.le,
            fun hit => hii.2.2 (Nat.lt_of_succ_lt_succ hit)⟩

theorem actualLimitPartPrefixAddition : Targets.ActualLimitPartPrefixAddition := by
  intro k hk r
  obtain ⟨q, hq⟩ := hk
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero r, mul_add]

end LogicLineages.OrdinalComparison
