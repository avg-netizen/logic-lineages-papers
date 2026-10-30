module
public import LogicLineages.OrdinalComparison.SuccessorMassResidualTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelMaximumProof
public import LogicLineages.OrdinalComparison.ReserveStageInputProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualSuccessorMassResidualAlgebra : Targets.ActualSuccessorMassResidualAlgebra := by
  intro gamma hg he B c e hce heB hbudget
  dsimp only
  let theta := Ordinal.omega0^gamma
  let L := theta*Ordinal.omega0
  let w := actualOrdinalNorm theta
  let q := (B-e)/w
  let qc := (B-c)/w
  let re := actualMaximumPredecessor theta ((B-e)%w)
  let rc := actualMaximumPredecessor theta ((B-c)%w)
  let rhi := theta*((qc-q : Nat) : Ordinal)+rc
  have hw : 0 < w := actualSuccessorPrincipalWeight gamma hg he
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le hw).mpr hbudget
  have hqqc : q ≤ qc := Nat.div_le_div_right (by omega : B-e ≤ B-c)
  have htheta : theta < epsilonZero := (Ordinal.le_mul_left theta Ordinal.omega0_pos).trans_lt he
  have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hg)
  have hre : re < theta := (actualMaximumPredecessor_correct theta hl.bot_lt htheta ((B-e)%w)).1.1
  have hrc : rc < theta := (actualMaximumPredecessor_correct theta hl.bot_lt htheta ((B-c)%w)).1.1
  have hNr : actualOrdinalNorm re=(B-e)%w := actualLimitMaximumPredecessorSaturation theta htheta hl _
  have hNc : actualOrdinalNorm rc=(B-c)%w := actualLimitMaximumPredecessorSaturation theta htheta hl _
  have hrhi : rhi < L := by
    change theta*((qc-q : Nat) : Ordinal)+rc < theta*Ordinal.omega0
    rw [show theta*Ordinal.omega0=Ordinal.omega0^(gamma+1) from (Ordinal.opow_add_one _ _).symm]
    exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 (qc-q)) hrc (Order.lt_add_one_iff.mpr le_rfl)
  have hpm := reserveStagePrincipalMultipleFacts gamma htheta (qc-q)
  have hnorm := actualDivisiblePrefixNormAddition (theta*((qc-q : Nat) : Ordinal)) rc hpm.1
    (hrc.trans htheta) gamma ⟨((qc-q : Nat) : Ordinal), rfl⟩
    (hrc.trans (by
      change Ordinal.omega0^gamma < Ordinal.omega0^(gamma+1)
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl)))
  have hNhi : actualOrdinalNorm rhi=(qc-q)*w+(B-c)%w := by
    rw [hnorm.2, hpm.2, hNc]
  have hde : q*w+(B-e)%w=B-e := by
    simpa only [q, Nat.mul_comm] using Nat.div_add_mod (B-e) w
  have hdc : qc*w+(B-c)%w=B-c := by
    simpa only [qc, Nat.mul_comm] using Nat.div_add_mod (B-c) w
  have hdiff : q*w+(qc-q)*w=qc*w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hqqc]
  have htotalE : e+q*w+actualOrdinalNorm re=B := by rw [hNr]; omega
  have htotalC : c+q*w+actualOrdinalNorm rhi=B := by rw [hNhi]; omega
  have hNorder : actualOrdinalNorm re ≤ actualOrdinalNorm rhi := by omega
  have horder : re ≤ rhi := by
    by_cases hh : q=qc
    · have hmod : (B-e)%w ≤ (B-c)%w := by rw [hh] at hde; omega
      have hm := actualMaximumJointMonotone theta theta hl.bot_lt le_rfl htheta _ _ hmod
      simpa only [rhi, hh, Nat.sub_self, Nat.cast_zero, mul_zero, zero_add] using hm
    · have hd : 0 < qc-q := by omega
      have hp : theta ≤ theta*((qc-q : Nat) : Ordinal) :=
        Ordinal.le_mul_left _ (by exact_mod_cast hd)
      exact hre.le.trans (hp.trans le_self_add)
  have heqE : theta*(q : Ordinal)+re=actualMaximumPredecessor L (B-e) :=
    (actualSuccessorPrincipalMaximum gamma hg he (B-e)).symm
  have heqC : theta*(q : Ordinal)+rhi=actualMaximumPredecessor L (B-c) := by
    change theta*(q : Ordinal)+(theta*((qc-q : Nat) : Ordinal)+rc)=_
    rw [← add_assoc, ← mul_add, ← Nat.cast_add, Nat.add_sub_of_le hqqc]
    exact (actualSuccessorPrincipalMaximum gamma hg he (B-c)).symm
  exact ⟨hw, hq, hqqc, hre, hrhi, horder, hNorder, htotalE, htotalC, heqE, heqC⟩

theorem actualSuccessorMassChildDomains : Targets.ActualSuccessorMassChildDomains := by
  intro gamma hg he B c e hce heB hbudget
  dsimp only
  let w := actualOrdinalNorm (Ordinal.omega0^gamma)
  let q := (B-e)/w
  intro j hj hjq
  change j ≤ q at hjq
  change c+w*(j-1) < e+w*(j-1) ∧ e+w*(j-1)+w ≤ B ∧ e+w*(j-1) ≤ B-w
  have hdiv : q*w ≤ B-e := Nat.div_mul_le_self _ _
  have hmul := Nat.mul_le_mul_left w hjq
  have hstep : w*(j-1)+w=w*j := by
    calc
      w*(j-1)+w = w*((j-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = w*j := by rw [Nat.sub_add_cancel hj]
  have hbound : e+w*(j-1)+w ≤ B := by
    rw [Nat.add_assoc, hstep]
    rw [Nat.mul_comm w q] at hmul
    omega
  refine ⟨by omega, hbound, ?_⟩
  omega

end LogicLineages.OrdinalComparison
