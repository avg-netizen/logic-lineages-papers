module
public import LogicLineages.OrdinalComparison.LimitMassFirstTargets
public import LogicLineages.OrdinalComparison.LimitExponentMaximumProof
public import LogicLineages.OrdinalComparison.AffordableLeadingProof
public import LogicLineages.OrdinalComparison.ProfileDirectPackedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLimitMassFirstSuffixes : Targets.ActualLimitMassFirstSuffixes := by
  intro L beta hl hL E hv t c e hT hce he
  dsimp only
  let B := Phi t
  let pi_e := actualMaximumPredecessor L.1.repr (B-e)
  let pi_c := actualMaximumPredecessor L.1.repr (B-c)
  let delta_e := actualMaximumPredecessor beta (B-e-1)
  let delta_c := actualMaximumPredecessor beta (B-c-1)
  have hlarge : Ordinal.omega0 < L.1.repr := by
    rw [hL]
    simpa only [Ordinal.opow_one] using
      ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.one_lt_of_isSuccLimit hl))
  have hpow : Ordinal.omega0^beta < epsilonZero := by rw [← hL]; exact normalRepresentationSound L
  have heps : beta < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mp hpow
  have hfour : 4 ≤ t := (max_le_iff.mp hT).1
  have hH : profileReserveLeadingBound (profileBoundWord E) ≤ t :=
    (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hT).2).2).2).2
  have hB : 2*t < B := reserveStageTwoMulLtPhi t
  have hbe : 2 ≤ B-e := by omega
  have hbc : 2 ≤ B-c := by omega
  have hbudget : B-e < B-c := by omega
  have hfe := actualLimitExponentMaximum beta hl heps (B-e) (by omega)
  have hfc := actualLimitExponentMaximum beta hl heps (B-c) (by omega)
  have hde : 0 < delta_e := hfe.2.2.2.2.2 hbe
  have hdc : 0 < delta_c := hfc.2.2.2.2.2 hbc
  have hpe : pi_e=Ordinal.omega0^delta_e := by
    change actualMaximumPredecessor L.1.repr (B-e)=Ordinal.omega0^delta_e
    rw [hL]
    exact hfe.2.2.2.1
  have hpc : pi_c=Ordinal.omega0^delta_c := by
    change actualMaximumPredecessor L.1.repr (B-c)=Ordinal.omega0^delta_c
    rw [hL]
    exact hfc.2.2.2.1
  have hdel : delta_e < delta_c := actualLimitExponentBudgetStrict beta hl heps (B-e) (B-c) (by omega) hbudget
  have hstrict : pi_e < pi_c := by
    rw [hpe, hpc]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hdel
  have homega : Ordinal.omega0 ≤ pi_e := by
    rw [hpe]
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.one_le_iff_pos.mpr hde)
  have hpcL : pi_c < L.1.repr :=
    (actualMaximumPredecessor_correct _ (Ordinal.omega0_pos.trans hlarge) (normalRepresentationSound L) (B-c)).1.1
  have hNe : actualOrdinalNorm pi_e=B-e := by rw [hpe]; exact hfe.2.2.2.2.1
  have hNc : actualOrdinalNorm pi_c=B-c := by rw [hpc]; exact hfc.2.2.2.2.1
  have hte : e+actualOrdinalNorm pi_e=B := by rw [hNe]; omega
  have htc : c+actualOrdinalNorm pi_c=B := by rw [hNc]; omega
  refine ⟨homega, hstrict, hpcL, hNe, hNc, hte, htc, ⟨delta_e, hde, hpe⟩, ⟨delta_c, hdc, hpc⟩, ?_⟩
  intro rho hr
  have hword := actualProfileBoundCompiler L.1.repr hlarge E hv
  have hh := hword.2.1 rho hr
  obtain ⟨delta, hd, hdelta, hle, _, hnorm⟩ := actualProfileLeadingMonomialCorrect rho hh.1
  have hN : actualOrdinalNorm (actualProfileLeadingMonomial rho) ≤ B-e := by
    rw [hnorm]
    have hm : profileLeadingWeight rho ≤ profileReserveLeadingBound (profileBoundWord E) :=
      List.le_max_of_le' 0 (List.mem_map.mpr ⟨rho, hr, rfl⟩) le_rfl
    exact hm.trans (hH.trans (by omega))
  have hAff := actualAffordableLeadingMaximum L ⟨beta, hL⟩ hlarge (B-e) hbe
  have hdom := hAff.2.2.2.2.2.2.2.2.2 delta (by rw [← hdelta]; exact hle.trans_lt hh.2)
    (by rw [← hdelta]; exact hN)
  rw [hdelta]
  exact hdom.trans hAff.2.2.2.2.1

end LogicLineages.OrdinalComparison
