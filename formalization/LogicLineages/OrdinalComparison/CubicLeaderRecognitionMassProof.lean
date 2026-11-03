module
public import LogicLineages.OrdinalComparison.SuccessorMassStepTargets
public import LogicLineages.OrdinalComparison.SuccessorMassCutProof
public import LogicLineages.OrdinalComparison.RepeatedResidualWordProof
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionRepeatedProof
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionDefinitions
public import LogicLineages.OrdinalComparison.KernelTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof

theorem actualSuccessorKernelStrictMassStep : LogicLineages.OrdinalComparison.Targets.ActualSuccessorKernelStrictMassStep := by
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

/-- Actual cubic strict mass, with the original cubic modulus and no
supplied comparator or child strictness premise. -/
theorem cubic_strict_mass (c e t : Nat) (hce : c < e)
    (ht : cubicModulus c e ≤ t) :
    CounterLeaderExpansion.kernel 3 e t < CounterLeaderExpansion.kernel 3 c t := by
  let eta : NONote := NONote.ofNat 2
  have hrepr : eta.1.repr = (2 : Ordinal) := by
    simp only [eta, NONote.ofNat, ONote.repr_ofNat, Nat.cast_ofNat]
  have hpos : 0 < eta.1.repr := by rw [hrepr]; norm_num
  have hstep : Ordinal.omega0 ^ eta.1.repr * Ordinal.omega0 =
      Ordinal.omega0 ^ (3 : Ordinal) := by
    rw [hrepr, ← Ordinal.opow_add_one]
    norm_num
  have heps : Ordinal.omega0 ^ eta.1.repr * Ordinal.omega0 < epsilonZero := by
    rw [hstep]
    exact finiteOmegaPowerBelowEpsilonZero 3
  have htwo : actualOrdinalNorm (Ordinal.omega0 ^ eta.1.repr) = 3 := by
    rw [hrepr]
    simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
      (actualFiniteMonomialFacts 2 1).2.1
  have hthree : actualOrdinalNorm (Ordinal.omega0 ^ eta.1.repr * Ordinal.omega0) = 4 := by
    rw [hstep]
    simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
      (actualFiniteMonomialFacts 3 1).2.1
  have hbound : max c e + 4 ≤ t :=
    (Nat.le_max_right 16 (max c e + 4)).trans ht
  have hdom : e + actualOrdinalNorm
      (Ordinal.omega0 ^ eta.1.repr * Ordinal.omega0) ≤ t := by
    rw [hthree]
    have hm := Nat.le_max_right c e
    omega
  have hPhi : t + 100 < Phi t := self_lt_fastControl 5 (t+100)
  have hbudget : 2 * actualOrdinalNorm (Ordinal.omega0 ^ eta.1.repr) ≤ Phi t - e := by
    rw [htwo]
    rw [hthree] at hdom
    omega
  have hcase : Ordinal.omega0 ^ eta.1.repr = Ordinal.omega0 ^ (2 : Ordinal) ∧
      (0 : Nat) = 0 := ⟨by rw [hrepr], rfl⟩
  have h := actualSuccessorKernelStrictMassStep eta hpos heps 0 (Or.inl hcase)
    t c e (Nat.zero_le t) hce hdom hbudget
  rw [hstep] at h
  exact h

end LogicLineages.OrdinalComparison.CubicLeaderRecognition.Proof
