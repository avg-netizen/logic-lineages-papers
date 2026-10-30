module
public import LogicLineages.OrdinalComparison.SuccessorKernelsTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelCutProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualSuccessorCountCocycle : Targets.ActualSuccessorCountCocycle := by
  intro gamma hg he c t
  dsimp only
  intro ht
  let theta := Ordinal.omega0 ^ gamma
  let L := theta * Ordinal.omega0
  let w := actualOrdinalNorm theta
  have hL : Ordinal.omega0 ^ (gamma + 1) = L := Ordinal.opow_add_one _ _
  have hgp : 0 < gamma + 1 := (lt_add_one gamma).trans_le' (le_of_lt hg)
  have he' : Ordinal.omega0 ^ (gamma + 1) < epsilonZero := by rw [hL]; exact he
  have hout := actualSuffixKernelInput (gamma + 1) hgp he' c t
    (by rw [hL]; change c + actualOrdinalNorm L ≤ t; change c + w + actualOrdinalNorm L ≤ t at ht; omega)
  rw [hL] at hout
  have hcut := actualSuccessorKernelCut gamma hg he c t ht
  dsimp only at hcut
  have hc := actualControlledCountTraceDecomposition (compensatedPrefixControl c)
    (actualSuffixKernelInitial L c t) hout.1 (actualSuffixKernelCount L (c + w) t) hcut.2.2.1
  rw [hcut.2.2.2] at hc
  change actualSuffixKernelCount L c t =
    actualSuffixKernelCount theta c (actualSuffixKernel L (c + w) t) +
      actualSuffixKernelCount L (c + w) t at hc
  exact hc.trans (Nat.add_comm _ _)

theorem actualSuccessorKernelComposition : Targets.ActualSuccessorKernelComposition := by
  intro gamma hg he c t
  dsimp only
  intro ht
  have hc := actualSuccessorCountCocycle gamma hg he c t ht
  unfold actualSuffixKernel
  rw [hc, Nat.add_comm, Function.iterate_add_apply]
  rfl

theorem fullActualSuccessorCutCocycle : Targets.FullActualSuccessorCutCocycle :=
  ⟨actualSuccessorCountCocycle, actualSuccessorKernelComposition⟩

end LogicLineages.OrdinalComparison
