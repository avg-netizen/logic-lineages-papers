module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.CalibrationProof
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsGrowthProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

/-- One quadratic block below the actual first suffix already pays the entire
integer-depth bound; it is evaluated at total input Phi(t), where its retained
mass domain is genuine. No broad source/old original-input equality is used. -/
private theorem depth_lower (d c : Nat) (j : Int) (t : Nat) (hd : 3 ≤ d)
    (hb : c+2*j.natAbs+6 ≤ Phi t) : (Phi t : Int) ≤ sourceSignedDepth d c j t := by
  let B := Phi t
  let pi := Ordinal.omega0 ^ (d : Ordinal)
  let Q := firstSuffix d c t
  let I := actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) c B
  have hcal := firstBudgetCalibration d c t (by omega) (by omega)
  have hQeps : Q < epsilonZero := hcal.2.1
  have htotalQ : c+actualOrdinalNorm Q = B := hcal.2.2.2.1
  have hcount : sourceCount d c t = actualControlledCount (compensatedPrefixControl c) Q+1 :=
    hcal.2.2.2.2.1
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have heps := finiteOmegaPowerBelowEpsilonZero d
  have hlim : Order.IsSuccLimit pi :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  have hw : Ordinal.omega0 ≤ Ordinal.omega0 ^ (2 : Ordinal) := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (show (1 : Ordinal) ≤ 2 by norm_num)
  have hdeg : (2 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 2 < d)
  have hsmall : Ordinal.omega0 ^ (2 : Ordinal) * 2 < pi := by
    simpa only [add_zero,Nat.cast_ofNat] using Ordinal.opow_mul_add_lt_opow
      (Ordinal.natCast_lt_omega0 2) (Ordinal.omega0_pos.trans_le hw) hdeg
  have hnormsmall : actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal) * 2) = 6 := by
    simpa using (actualFiniteMonomialFacts 2 2).2.1
  have hmax := actualMaximumPredecessor_correct pi hlim.bot_lt heps (B-c)
  have hsmallQ : Ordinal.omega0 ^ (2 : Ordinal) * 2 ≤ Q := by
    apply hmax.2
    refine ⟨hsmall,?_⟩
    rw [hnormsmall]
    dsimp only [B]
    omega
  have hIlt : I < Ordinal.omega0 ^ (2 : Ordinal) * 2 := by
    change Ordinal.omega0 ^ (2 : Ordinal) +
      ((B-c-actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)) : Nat) : Ordinal) < _
    rw [Ordinal.mul_two]
    exact (Ordinal.isNormal_add_right _).strictMono
      ((Ordinal.natCast_lt_omega0 _).trans_le hw)
  have hin := KernelCounterCalibrationProof.actualFiniteKernelInput 2 c B (by omega) (by omega)
  have hnorm : actualOrdinalNorm I ≤ actualOrdinalNorm Q := by
    have hi : c+actualOrdinalNorm I = B := hin.2.2.1
    omega
  have hcomp := actualControlledCountsJointMonotone (compensatedPrefixControl c)
    (compensatedPrefixControl c) (fun _ => le_rfl) (compensatedPrefixControlBounds c).1
    I Q (hIlt.le.trans hsmallQ) hQeps hnorm
  change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c B ≤
    actualControlledCount (compensatedPrefixControl c) Q at hcomp
  rw [actualOmegaSquaredSuffixCount c B (by omega)] at hcomp
  have hg := CounterLeaderBounds.Proof.four_mul_lt_Phi B
  have hbig : B+j.natAbs ≤ sourceCount d c t := by omega
  have hj : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
  change (B : Int) ≤ (sourceCount d c t : Int)+j
  omega

private theorem positive_depth_output (d c : Nat) (j : Int) (t : Nat)
    (h : 0 < sourceSignedDepth d c j t) : Phi t ≤ sourceSignedValue d c j t := by
  have hn : 1 ≤ (sourceSignedDepth d c j t).toNat := by omega
  change (Phi^[1]) t ≤ (Phi^[(sourceSignedDepth d c j t).toNat]) t
  exact iterate_index_mono (fun x => (self_lt_Phi x).le) t hn

theorem uniformDepthAndOutputBounds : Targets.UniformDepthAndOutputBounds := by
  intro d c e j k R t hd hr
  have hd1 : 1 ≤ d := by omega
  have h1 : 1000 ≤ 1000*d := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 1000 hd1
  have h2 : 1000*d ≤ 1000*d*d := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (1000*d) hd1
  have hC : 6 ≤ degreeConstant d := (by omega : 6 ≤ 1000).trans (h1.trans h2)
  have hbudget : 6*(c+e+j.natAbs+k.natAbs+R+1) ≤ Phi t :=
    (Nat.mul_le_mul_right _ hC).trans hr.2
  have hc : c+2*j.natAbs+6 ≤ Phi t := by omega
  have he : e+2*k.natAbs+6 ≤ Phi t := by omega
  have hm : Phi t ≤ Phi (t+1) := Phi_strictMono.monotone (by omega)
  have hmI : (Phi t : Int) ≤ (Phi (t+1) : Int) := by exact_mod_cast hm
  have hc0 := depth_lower d c j t hd hc
  have he0 := depth_lower d e k t hd he
  have hc1 := depth_lower d c j (t+1) hd (hc.trans hm)
  have he1 := depth_lower d e k (t+1) hd (he.trans hm)
  have hp : (0 : Int) < (Phi t : Int) := by have := self_lt_Phi t; omega
  have hp1 : (0 : Int) < (Phi (t+1) : Int) := hp.trans_le hmI
  exact ⟨hc0,he0,hmI.trans hc1,hmI.trans he1,
    positive_depth_output d c j t (hp.trans_le hc0),
    positive_depth_output d e k t (hp.trans_le he0),
    hm.trans (positive_depth_output d c j (t+1) (hp1.trans_le hc1)),
    hm.trans (positive_depth_output d e k (t+1) (hp1.trans_le he1))⟩

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
