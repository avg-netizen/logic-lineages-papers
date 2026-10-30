module

public import LogicLineages.OrdinalComparison.SignedKernelDomainTargets
public import LogicLineages.OrdinalComparison.KernelCounterCalibrationProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof
public import LogicLineages.OrdinalComparison.ControlledCountProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedKernelDomainProof
open KernelCounterCalibrationProof

private theorem degree_count_comparison (d c t : Nat) (hd : 2 ≤ d) (ht : c + d + 1 ≤ t) :
    actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t ≤
      actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t := by
  by_cases heq : d = 2
  · subst d; exact le_rfl
  have hin2 := actualFiniteKernelInput 2 c t (by omega) (by omega)
  have hind := actualFiniteKernelInput d c t (by omega) ht
  have hlt : actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) c t <
      Ordinal.omega0 ^ (d : Ordinal) := by
    have hω : Ordinal.omega0 ≤ Ordinal.omega0 ^ (2 : Ordinal) := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (show (1 : Ordinal) ≤ 2 by norm_num)
    have htail := (Ordinal.natCast_lt_omega0
      (t - c - actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)))).trans_le hω
    have hdeg : (2 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 2 < d)
    simpa only [actualSuffixKernelInitial, Nat.cast_one, mul_one] using
      Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 1) htail hdeg
  apply actualControlledCountsJointMonotone (compensatedPrefixControl c) (compensatedPrefixControl c)
    (fun _ => le_rfl) (compensatedPrefixControlBounds c).1 _ _
    (hlt.le.trans le_self_add) hind.2.1
  change actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) c t) ≤
    actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t)
  have h2 : c + actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) c t) = t := by
    simpa using hin2.2.2.1
  have hd' := hind.2.2.1
  omega

theorem finiteDegreeCounterLowerBound : Targets.FiniteDegreeCounterLowerBound := by
  refine ⟨degree_count_comparison, ?_⟩
  intro d c k t hd ht
  have hdom : c + d + 1 ≤ t := (Nat.le_max_left _ _).trans ht
  have hlarge : c + 2 * k + 3 ≤ t := (Nat.le_max_right _ _).trans ht
  have hcomp := degree_count_comparison d c t hd hdom
  rw [actualOmegaSquaredSuffixCount c t (by omega)] at hcomp
  have hg := self_lt_Phi t
  omega

theorem degreeOneSignedDomain : Targets.DegreeOneSignedDomain := by
  intro c t ht j
  have hc := (actualOmegaSuffixKernel c t ht).1
  have hdepth : signedKernelDepth 1 c j t = 1 + j := by
    simp only [signedKernelDepth, Nat.cast_one, Ordinal.opow_one, hc, Int.natCast_one]
  exact ⟨hdepth, by rw [hdepth]; omega⟩

theorem degreeOneNegativeDepthObstruction : Targets.DegreeOneNegativeDepthObstruction := by
  intro c j hj h
  obtain ⟨T, hT⟩ := h
  have hp := hT (max T (c + 2)) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hnonneg := (degreeOneSignedDomain c (max T (c + 2)) (Nat.le_max_right _ _) j).2.mp hp
  omega

theorem genuineSignedKernelResidueAndCoherence : Targets.GenuineSignedKernelResidueAndCoherence := by
  intro d c j t hpos
  have hsucc : (signedKernelDepth d c (j + 1) t).toNat = (signedKernelDepth d c j t).toNat + 1 := by
    dsimp [signedKernelDepth] at *
    omega
  constructor
  · unfold rawSignedKernelValue
    rw [hsucc, Function.iterate_succ_apply']
  · intro m hm ht
    have hn : 0 < (signedKernelDepth d c j t).toNat := by omega
    have hnEq : (signedKernelDepth d c j t).toNat = ((signedKernelDepth d c j t).toNat - 1) + 1 := by omega
    unfold rawSignedKernelValue
    rw [hnEq, Function.iterate_succ_apply']
    apply phiShiftedConstantResidues m (by omega)
    exact (Nat.sub_le _ _).trans (ht.trans (iterate_self_le (fun x => (self_lt_Phi x).le) _ t))

theorem correctedSignedKernelResidues : Targets.CorrectedSignedKernelResidues := by
  intro d c j hreg m hm t ht
  have hmt : m ≤ t := (Nat.le_max_left _ _).trans ht
  have htail : max (c + d + 1) (c + 2 * j.natAbs + 3) ≤ t := (Nat.le_max_right _ _).trans ht
  have hdom : c + d + 1 ≤ t := (Nat.le_max_left _ _).trans htail
  have hpos : 0 < signedKernelDepth d c j t := by
    rcases hreg with hd | ⟨rfl, hj⟩
    · have hlarge := finiteDegreeCounterLowerBound.2 d c j.natAbs t hd htail
      have hj : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
      dsimp [signedKernelDepth]
      omega
    · exact (degreeOneSignedDomain c t (by omega) j).2.mpr hj
  exact ⟨hpos, (genuineSignedKernelResidueAndCoherence d c j t hpos).2 m hm hmt⟩

theorem fixedSignedKernelThresholdPrimitiveRecursive : Targets.FixedSignedKernelThresholdPrimitiveRecursive := by
  intro j
  have hd : Primrec (fun z : Nat × Nat × Nat => z.1) := Primrec.fst
  have hc : Primrec (fun z : Nat × Nat × Nat => z.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun z : Nat × Nat × Nat => z.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_max.comp hm (Primrec.nat_max.comp
    (Primrec.succ.comp (Primrec.nat_add.comp hc hd))
    (Primrec.nat_add.comp (Primrec.nat_add.comp hc (Primrec.const (2 * j.natAbs))) (Primrec.const 3)))

end LogicLineages.OrdinalComparison.SignedKernelDomainProof
