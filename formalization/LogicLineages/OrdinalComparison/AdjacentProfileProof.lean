module
public import LogicLineages.OrdinalComparison.AdjacentProfileTargets
public import LogicLineages.OrdinalComparison.AdjacentReserveCutProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

-- Auditor-approved root-delegated local allowance after 1793353390307878337-8.
set_option maxHeartbeats 400000 in
theorem actualAdjacentProfileSeparation : Targets.ActualAdjacentProfileSeparation := by
  intro L hp hlarge E hv t c e hT hc he
  let B := Phi t
  let B' := Phi (t+1)
  let b := actualMaximumPredecessor L.1.repr (B-e)
  let pi := (profileLeadingNote (maximumPredecessor L (B-e))).1.repr
  let R := profileReserveBlocks (profileBoundWord E)
  let p := c+R*actualOrdinalNorm pi
  let k := (B'+e)-(B+p)
  let A := pi*(R : Ordinal)+(b+(k : Ordinal))
  let Q := actualMaximumPredecessor L.1.repr (B'-c)
  let D := actualSuffixKernelCount L.1.repr e t
  let Z := actualSuffixKernel L.1.repr e t
  let q := actualControlledCount (compensatedPrefixControl p) (b+(k : Ordinal))
  let n := (Phi^[q]) B'-p
  let g := compensatedPrefixControl c
  have hpack := actualAdjacentPackedState L hp hlarge E hv t c e hT hc he
  have hcut := actualAdjacentReserveCut L hp hlarge E hv t c e hT hc he
  have hlead := actualAdjacentLeadingCoverage L hp hlarge E hv t e hT he
  obtain ⟨ell, hL⟩ := hp
  have hell : (1 : Ordinal) < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [Ordinal.opow_one, ← hL]; exact hlarge)
  have hep := zero_lt_one.trans hell
  have heL := normalRepresentationSound L
  have hel : Ordinal.omega0^ell < epsilonZero := by rw [← hL]; exact heL
  have hreserve := fullActualEffectiveProfileReserve ell (by rw [← hL]; exact hlarge) hel E
    (by rw [← hL]; exact hv)
  have hz0 : fixedLimitProfileThreshold E ≤ t :=
    (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hT).2).2).1
  have htZ : t ≤ Z := by
    change t ≤ (Phi^[D]) t
    have hh := iterate_index_mono (fun x => (self_lt_Phi x).le) t (Nat.zero_le D)
    simpa only [Function.iterate_zero_apply] using hh
  have hz : fixedLimitProfileThreshold E ≤ Z+D := hz0.trans (htZ.trans (Nat.le_add_right _ _))
  obtain ⟨gamma, hg, hpi⟩ := hlead.2.2.2.2.1
  change pi=Ordinal.omega0^gamma at hpi
  have hpieps : Ordinal.omega0^gamma < epsilonZero := by rw [← hpi]; exact hlead.2.2.1.trans heL
  have hhead : ∀ rho ∈ profileBoundWord E, actualProfileLeadingMonomial rho ≤ Ordinal.omega0^gamma := by
    rw [← hpi]
    exact hlead.2.2.2.2.2
  have hzn : Z+D < n := hcut.2.2.2.2.2.2.2
  have hs := (((hreserve.2.2.2.2 (Z+D) hz).2 gamma hg hpieps hhead n hzn.le).2 c)
  have hS : actualFixedLimitProfileEval E (Z+D) < c+actualOrdinalNorm
      (actualControlledStateAfter g (pi*(R : Ordinal)+(n : Ordinal))
        (actualControlledCount g (pi*(R : Ordinal)+(n : Ordinal)))) := by
    simpa only [← hpi] using hs
  have hA : A < epsilonZero := hpack.2.2.2.2.1.trans heL
  have hendpoint := actualControlledEndpointAlongTrace g A hA q hcut.2.2.1
  have hentry : actualControlledStateAfter g A q=pi*(R : Ordinal)+(n : Ordinal) := hcut.2.2.2.2.2.2.1
  rw [hentry] at hendpoint
  rw [hendpoint] at hS
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hep)
  have hQ : Q < epsilonZero :=
    (actualMaximumPredecessor_correct L.1.repr (by rw [hL]; exact hlim.bot_lt) heL (B'-c)).1.1.trans heL
  have hnorm : actualOrdinalNorm A ≤ actualOrdinalNorm Q := by
    rw [hpack.2.2.2.2.2.2.2.2.1, hpack.2.2.2.2.2.2.2.2.2.2]
  have hb := compensatedPrefixControlBounds c
  have hm := actualControlledExitNormMonotone g hb.1 (fun x => (hb.2 x).2.le) A Q
    hpack.2.2.2.2.2.2.2.2.2.1 hQ hnorm
  have hfirst := actualSuffixKernelFirstMaximum ell hep hel c (t+1) (by rw [← hL]; exact hc)
  have hK : actualSuffixKernel L.1.repr c (t+1)=c+actualOrdinalNorm
      (actualControlledStateAfter g Q (actualControlledCount g Q)) := by
    simpa only [← hL] using hfirst.2.2
  exact (hS.trans_le (Nat.add_le_add_left hm c)).trans_eq hK.symm

theorem actualCrossMassProfileSeparation : Targets.ActualCrossMassProfileSeparation := by
  intro L hp hlarge E hv t u c e hT htu hc he
  let N := actualOrdinalNorm L.1.repr
  have htN : N ≤ t := (Nat.le_add_left _ e).trans he
  have ht1 : N ≤ t+1 := htN.trans (Nat.le_succ t)
  have hu : N ≤ u := htN.trans htu.le
  have hadj := actualAdjacentProfileSeparation L hp hlarge E hv t (t+1-N) e hT
    (Nat.sub_add_cancel ht1).le he
  obtain ⟨beta, hL⟩ := hp
  have hb : (1 : Ordinal) < beta := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [Ordinal.opow_one, ← hL]; exact hlarge)
  have heps : Ordinal.omega0^beta < epsilonZero := by rw [← hL]; exact normalRepresentationSound L
  have hw := actualWorstMassKernelMonotone beta (zero_lt_one.trans hb) heps (t+1) u
    (by rw [← hL]; exact ht1) htu
  have hmass : c ≤ u-N := by omega
  have hm := actualSuffixKernelInputMassMonotone beta (zero_lt_one.trans hb) heps c (u-N) u u
    hmass le_rfl (by rw [← hL]; exact (Nat.sub_add_cancel hu).le) (by rw [← hL]; exact hc)
  rw [← hL] at hw hm
  exact hadj.trans_le (hw.trans hm)

private theorem adjacent_affine_growth (a b t : Nat) (ht : a+b+2 ≤ t) :
    a*(Phi t+1)+b < Phi (t+1) := by
  let B := Phi t
  have hB : t < B := self_lt_Phi t
  have hnum : a*(B+1)+b ≤ B*B := by
    have hm := Nat.mul_le_mul_right B (by omega : a+1 ≤ B)
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hm ⊢
    omega
  have hp : 0 < B := by omega
  have htwo : B < 2^B := Nat.lt_two_pow_self
  have hsq := (Nat.mul_lt_mul_of_pos_left htwo hp).trans_le (Nat.mul_le_mul_right (2^B) htwo.le)
  rw [← Nat.pow_add] at hsq
  have hexp : B+B ≤ 2^(B+1) := by rw [Nat.pow_succ]; omega
  exact hnum.trans_lt ((hsq.trans_le (Nat.pow_le_pow_right (by decide) hexp)).trans_le (Phi_succ_gap t))

theorem actualOmegaAffineCrossMassSeparation : Targets.ActualOmegaAffineCrossMassSeparation := by
  intro a b t u c e ht htu hc he
  have hlo := actualOmegaSuffixKernel e t he
  have hhi := actualOmegaSuffixKernel c u hc
  rw [hlo.1, hlo.2, hhi.2]
  exact (adjacent_affine_growth a b t (max_le_iff.mp ht).2).trans_le (Phi_strictMono.monotone htu)

theorem fullActualCrossMassStrictInputSeparation : Targets.FullActualCrossMassStrictInputSeparation :=
  ⟨actualAdjacentProfileSeparation, actualCrossMassProfileSeparation, actualOmegaAffineCrossMassSeparation⟩

end LogicLineages.OrdinalComparison
