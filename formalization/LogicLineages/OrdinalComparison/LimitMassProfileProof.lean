module
public import LogicLineages.OrdinalComparison.LimitMassProfileTargets
public import LogicLineages.OrdinalComparison.LimitMassReserveCutProof
public import LogicLineages.OrdinalComparison.AdjacentProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLimitMassProfileSeparation : Targets.ActualLimitMassProfileSeparation := by
  intro L beta hl hL E hv t c e hT hce he
  let B := Phi t
  let C := Phi B
  let pe := actualMaximumPredecessor L.1.repr (B-e)
  let pc := actualMaximumPredecessor L.1.repr (B-c)
  let R := profileReserveBlocks (profileBoundWord E)
  let p := c+R*actualOrdinalNorm pe
  let k := C-(c+(R+1)*actualOrdinalNorm pe)
  let r := pe+(k : Ordinal)
  let A := pe*(R : Ordinal)+r
  let Q := actualMaximumPredecessor pc (C-c)
  let D := actualSuffixKernelCount L.1.repr e t
  let Z := actualSuffixKernel L.1.repr e t
  let q := actualControlledCount (compensatedPrefixControl p) r
  let n := (Phi^[q]) C-p
  let g := compensatedPrefixControl c
  have hf := actualLimitMassFirstSuffixes L beta hl hL E hv t c e hT hce he
  have hpack := actualLimitMassPackedState L beta hl hL E hv t c e hT hce he
  have hcut := actualLimitMassReserveCut L beta hl hL E hv t c e hT hce he
  have hlarge : Ordinal.omega0 < L.1.repr := by
    rw [hL]
    simpa only [Ordinal.opow_one] using
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.one_lt_of_isSuccLimit hl))
  have heL := normalRepresentationSound L
  have hel : Ordinal.omega0^beta < epsilonZero := by rw [← hL]; exact heL
  have hreserve := fullActualEffectiveProfileReserve beta (by rw [← hL]; exact hlarge) hel E
    (by rw [← hL]; exact hv)
  have hz0 : fixedLimitProfileThreshold E ≤ t :=
    (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hT).2).2).1
  have htZ : t ≤ Z := by
    change t ≤ (Phi^[D]) t
    have hh := iterate_index_mono (fun x => (self_lt_Phi x).le) t (Nat.zero_le D)
    simpa only [Function.iterate_zero_apply] using hh
  have hz : fixedLimitProfileThreshold E ≤ Z+D := hz0.trans (htZ.trans (Nat.le_add_right _ _))
  obtain ⟨gamma, hg, hpe⟩ := hf.2.2.2.2.2.2.2.1
  change pe=Ordinal.omega0^gamma at hpe
  have hpcE : pc < epsilonZero := hf.2.2.1.trans heL
  have hpeE : pe < epsilonZero := hf.2.1.trans hpcE
  have hpow : Ordinal.omega0^gamma < epsilonZero := by rw [← hpe]; exact hpeE
  have hhead : ∀ rho ∈ profileBoundWord E, actualProfileLeadingMonomial rho ≤ Ordinal.omega0^gamma := by
    rw [← hpe]
    exact hf.2.2.2.2.2.2.2.2.2
  have hzn : Z+D < n := hcut.2.2.2.2.2.2.2
  have hs := (((hreserve.2.2.2.2 (Z+D) hz).2 gamma hg hpow hhead n hzn.le).2 c)
  have hS : actualFixedLimitProfileEval E (Z+D) < c+actualOrdinalNorm
      (actualControlledStateAfter g (pe*(R : Ordinal)+(n : Ordinal))
        (actualControlledCount g (pe*(R : Ordinal)+(n : Ordinal)))) := by
    simpa only [← hpe] using hs
  have hA : A < epsilonZero := hpack.2.2.2.1.trans hpcE
  have hendpoint := actualControlledEndpointAlongTrace g A hA q hcut.2.2.1
  have hentry : actualControlledStateAfter g A q=pe*(R : Ordinal)+(n : Ordinal) := hcut.2.2.2.2.2.2.1
  rw [hentry] at hendpoint
  rw [hendpoint] at hS
  obtain ⟨delta, hd, hpc⟩ := hf.2.2.2.2.2.2.2.2.1
  change pc=Ordinal.omega0^delta at hpc
  have hlim : Order.IsSuccLimit pc := by
    rw [hpc]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hd)
  have hQ : Q < epsilonZero := (actualMaximumPredecessor_correct pc hlim.bot_lt hpcE (C-c)).1.1.trans hpcE
  have hnorm : actualOrdinalNorm A ≤ actualOrdinalNorm Q := by
    rw [hpack.2.2.2.2.1, hpack.2.2.2.2.2.1]
  have hb := compensatedPrefixControlBounds c
  have hm := actualControlledExitNormMonotone g hb.1 (fun x => (hb.2 x).2.le) A Q
    hpack.2.2.2.2.2.2.1 hQ hnorm
  have hsecond := actualLimitMassSecondMaximum L beta hl hL E hv t c e hT hce he
  have hK : actualSuffixKernel L.1.repr c t=c+actualOrdinalNorm
      (actualControlledStateAfter g Q (actualControlledCount g Q)) := hsecond.2.2
  exact (hS.trans_le (Nat.add_le_add_left hm c)).trans_eq hK.symm

theorem actualLimitLexicographicSeparation : Targets.ActualLimitLexicographicSeparation := by
  intro L beta hl hL E hv t u c e hT hc he
  have hlarge : Ordinal.omega0 < L.1.repr := by
    rw [hL]
    simpa only [Ordinal.opow_one] using
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.one_lt_of_isSuccLimit hl))
  constructor
  · intro h
    rcases h with htu | ⟨rfl, hce⟩
    · exact actualCrossMassProfileSeparation L ⟨beta, hL⟩ hlarge E hv t u c e
        (max_le_iff.mp hT).2 htu hc he
    · exact actualLimitMassProfileSeparation L beta hl hL E hv t c e (max_le_iff.mp hT).1 hce he
  · rintro ⟨rfl, rfl⟩
    rfl

theorem fullActualLimitExponentMassSeparation : Targets.FullActualLimitExponentMassSeparation :=
  ⟨actualLimitMassProfileSeparation, actualLimitLexicographicSeparation⟩

end LogicLineages.OrdinalComparison
