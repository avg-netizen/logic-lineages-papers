module
public import LogicLineages.OrdinalComparison.ControlScheduleTargets
public import LogicLineages.OrdinalComparison.ScheduledCountProof
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualControlBudgetStreamTrace : Targets.ActualControlBudgetStreamTrace := by
  intro g a i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [actualScheduledStateLastStep, actualControlledStateAfter_succ, ih]
    rfl

theorem actualControlBudgetStreamCount : Targets.ActualControlBudgetStreamCount := by
  intro g a ha
  have hs := actualScheduledFirstFinite (actualControlBudgetStream g a) a ha
  have hc := actualControlledTraceFirstFinite g a ha
  apply Nat.le_antisymm
  · by_contra hn
    have hlt : actualControlledCount g a < actualScheduledCount (actualControlBudgetStream g a) a :=
      Nat.lt_of_not_ge hn
    have hnon := (hs.2 _ hlt.le).2.2 hlt
    rw [actualControlBudgetStreamTrace] at hnon
    exact not_lt_of_ge hnon hc.1
  · by_contra hn
    have hlt : actualScheduledCount (actualControlBudgetStream g a) a < actualControlledCount g a :=
      Nat.lt_of_not_ge hn
    have hnon := (hc.2 _ hlt.le).2.2 hlt
    have hfinite := hs.1
    rw [actualControlBudgetStreamTrace] at hfinite
    exact not_lt_of_ge hnon hfinite

theorem actualControlledNormIteration : Targets.ActualControlledNormIteration := by
  intro g a ha i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hlt : i < actualControlledCount g a := by omega
    have hs := (actualControlledTraceFirstFinite g a ha).2 i hlt.le
    rw [actualControlledStateAfter_succ, actualControlledStepNorm g _ (hs.2.2 hlt) hs.1,
      ih hlt.le, Function.iterate_succ_apply']

end LogicLineages.OrdinalComparison
