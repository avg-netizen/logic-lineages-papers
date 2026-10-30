module
public import LogicLineages.OrdinalComparison.ControlledStepTargets
public import LogicLineages.OrdinalComparison.ActualTailSeparation

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualControlledStepStrict : Targets.ActualControlledStepStrict := by
  intro g a hn ha
  have hd := actualNonfiniteDecomposition a hn ha
  have hm := actualMaximumPredecessor_correct (actualLimitPart a) hd.2.1.bot_lt hd.1
    (g (actualOrdinalNorm a))
  exact hm.1.1.trans_le (Ordinal.mul_div_le a Ordinal.omega0)

theorem actualControlledStepNorm : Targets.ActualControlledStepNorm := by
  intro g a hn ha
  have hd := actualNonfiniteDecomposition a hn ha
  exact actualLimitMaximumPredecessorSaturation (actualLimitPart a) hd.1 hd.2.1
    (g (actualOrdinalNorm a))

theorem actualControlledStepsJointMonotone : Targets.ActualControlledStepsJointMonotone := by
  intro g h hgh hmono a a' hn haa heps hnorm
  have ha := haa.trans_lt heps
  have hn' := hn.trans haa
  have hd := actualNonfiniteDecomposition a hn ha
  have hd' := actualNonfiniteDecomposition a' hn' heps
  have hbudget : g (actualOrdinalNorm a) ≤ h (actualOrdinalNorm a') :=
    (hgh _).trans (hmono hnorm)
  constructor
  · exact actualMaximumJointMonotone _ _ hd.2.1.bot_lt
      (actualLimitPartMonotone haa) hd'.1 _ _ hbudget
  · rw [actualControlledStepNorm g a hn ha, actualControlledStepNorm h a' hn' heps]
    exact hbudget

end LogicLineages.OrdinalComparison
