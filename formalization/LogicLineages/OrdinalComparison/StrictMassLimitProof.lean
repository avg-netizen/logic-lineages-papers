module
public import LogicLineages.OrdinalComparison.StrictMassLimitTargets
public import LogicLineages.OrdinalComparison.LimitMassProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualIdentityProfileCalibration : Targets.ActualIdentityProfileCalibration := by
  have hR : profileReserveBlocks (profileBoundWord .input)=3 := by decide
  have hH : profileReserveLeadingBound (profileBoundWord .input)=2 := by decide
  refine ⟨rfl, hR, hH, rfl, ?_⟩
  intro L
  unfold profileLimitMassThreshold
  rw [hR, hH, actualOrdinalNorm_notationCorrespondence L]
  change max 4 (max 7 (max 4 (max (Vendor.R1.treeWeight L.1+1) 2))) =
    max 7 (Vendor.R1.treeWeight L.1+1)
  omega

theorem actualLimitKernelStrictMass : Targets.ActualLimitKernelStrictMass := by
  intro L beta hl hL t c e ht hce he
  have hthreshold : profileLimitMassThreshold L .input ≤ t := by
    rw [actualIdentityProfileCalibration.2.2.2.2 L]
    exact ht
  have h := actualLimitMassProfileSeparation L beta hl hL .input (by trivial) t c e hthreshold hce he
  change actualSuffixKernel L.1.repr e t+actualSuffixKernelCount L.1.repr e t < actualSuffixKernel L.1.repr c t at h
  exact (Nat.le_add_right _ _).trans_lt h

end LogicLineages.OrdinalComparison
