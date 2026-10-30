module
public import LogicLineages.OrdinalComparison.SuccessorMassStepTargets
public import LogicLineages.OrdinalComparison.SuccessorMassCutProof
public import LogicLineages.OrdinalComparison.RepeatedResidualWordProof
public import LogicLineages.OrdinalComparison.RepeatedWordOrderProof
public import LogicLineages.OrdinalComparison.KernelTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualSuccessorKernelStrictMassStep : Targets.ActualSuccessorKernelStrictMassStep := by
  intro eta heta hL S hcase t c e hS hce het hbudget
  let gamma := eta.1.repr
  let theta := Ordinal.omega0^gamma
  let L := theta*Ordinal.omega0
  let w := actualOrdinalNorm theta
  let B := Phi t
  let q := (B-e)/w
  let qc := (B-c)/w
  let re := actualMaximumPredecessor theta ((B-e)%w)
  let rc := actualMaximumPredecessor theta ((B-c)%w)
  let rhi := theta*((qc-q : Nat) : Ordinal)+rc
  let pe := e+q*w
  let pc := c+q*w
  let Ce := actualControlledCount (compensatedPrefixControl pe) re
  let Cc := actualControlledCount (compensatedPrefixControl pc) rhi
  let Ue := (Phi^[Ce]) B
  let Uc := (Phi^[Cc]) B
  have htB : t ≤ B := (self_lt_Phi t).le
  have heB : e ≤ B := by omega
  have hd := actualSuccessorMassResidualAlgebra gamma heta hL B c e hce heB hbudget
  have hcut := actualSuccessorMassResidualCuts gamma heta hL B c e hce heB hbudget
  have htheta : theta < epsilonZero := (Ordinal.le_mul_left theta Ordinal.omega0_pos).trans_lt hL
  have hre : re < theta := hd.2.2.2.1
  have hrhi : rhi < L := hd.2.2.2.2.1
  have hsumE : e+q*w+actualOrdinalNorm re=B := hd.2.2.2.2.2.2.2.1
  have hsumC : c+q*w+actualOrdinalNorm rhi=B := hd.2.2.2.2.2.2.2.2.1
  have hstateE : theta*(q : Ordinal)+re=actualMaximumPredecessor L (B-e) := hd.2.2.2.2.2.2.2.2.2.1
  have hstateC : theta*(q : Ordinal)+rhi=actualMaximumPredecessor L (B-c) := hd.2.2.2.2.2.2.2.2.2.2
  have hcalE := actualRepeatedResidualWordCalibration eta heta hL q e re
    (hre.trans_le (Ordinal.le_mul_left theta Ordinal.omega0_pos))
  have hcalC := actualRepeatedResidualWordCalibration eta heta hL q c rhi hrhi
  dsimp only at hcalE hcalC
  rw [hsumE, hstateE] at hcalE
  rw [hsumC, hstateC] at hcalC
  have hword := actualRepeatedWordStrictMass eta heta S hcase q c e Ue Uc hd.2.1 hce
    (hS.trans (htB.trans hcut.2.1)) hcut.2.2.2.2.2.2.2.1 hcut.2.2.1
  have hgamma : 0 < gamma+1 := (show (0 : Ordinal) ≤ gamma from zero_le).trans_lt (Order.lt_add_one_iff.mpr le_rfl)
  have hLe : Ordinal.omega0^(gamma+1)<epsilonZero := by rw [Ordinal.opow_add_one]; exact hL
  have hetL : e+actualOrdinalNorm L ≤ t := het
  have hct : c+actualOrdinalNorm L ≤ t := by omega
  have hfirstE := actualSuffixKernelFirstMaximum (gamma+1) hgamma hLe e t (by simpa only [Ordinal.opow_add_one] using het)
  have hfirstC := actualSuffixKernelFirstMaximum (gamma+1) hgamma hLe c t (by simpa only [Ordinal.opow_add_one] using hct)
  dsimp only at hfirstE hfirstC
  rw [Ordinal.opow_add_one] at hfirstE hfirstC
  change actualSuffixKernel L e t < actualSuffixKernel L c t
  rw [hfirstE.2.2, hfirstC.2.2]
  rw [← hcalE.2.2.1, ← hcalC.2.2.1]
  exact hword

end LogicLineages.OrdinalComparison
