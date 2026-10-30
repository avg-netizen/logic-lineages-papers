module
public import LogicLineages.OrdinalComparison.ProfileDirectPackedTargets
public import LogicLineages.OrdinalComparison.ProfileDominatorProof
public import LogicLineages.OrdinalComparison.ProfileReserveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem profileThreeMulLtPhi (t : Nat) : 3 * t < Phi t := by
  have hh : t < 2 ^ t := Nat.lt_two_pow_self
  have hp : 2 ^ (t + 2) = 2 ^ t * 4 := by rw [Nat.pow_add]
  have h3 : 3 * t < 2 ^ (t + 2) := by rw [hp]; omega
  exact h3.trans_le ((Nat.pow_le_pow_right (by decide) (by omega : t + 2 ≤ t + 100)).trans
    (two_pow_shift_le_Phi t))

theorem actualProfileDirectPackedState : Targets.ActualProfileDirectPackedState := by
  intro L hprincipal hlarge E hv t c hT hc
  dsimp only
  let word := profileBoundWord E
  let R := profileReserveBlocks word
  let pi := (profilePrincipalDominator word).1.repr
  let S := pi * (R : Ordinal) + (t : Ordinal)
  let Q := actualMaximumPredecessor L.1.repr (Phi t-c)
  have hcompiler := actualProfileBoundCompiler L.1.repr hlarge E hv
  have hdom := actualProfilePrincipalDominator L.1.repr hlarge word hcompiler.2.1
  have hthreshold := actualProfileDirectThresholdCalibration L E
  rw [hthreshold] at hT
  have hRbound : R * actualOrdinalNorm pi ≤ t := (max_le_iff.mp (max_le_iff.mp hT).2).1
  obtain ⟨gamma, hg, hpi⟩ := hdom.2.2.2.2
  change pi = Ordinal.omega0 ^ gamma at hpi
  obtain ⟨ell, hL⟩ := hprincipal
  have hge : gamma < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [← hpi, ← hL]
    exact hdom.2.1)
  have hsmall : S < L.1.repr := by
    change pi * (R : Ordinal) + (t : Ordinal) < L.1.repr
    have htail : (t : Ordinal) < Ordinal.omega0 ^ gamma := by
      rw [← hpi]
      exact (Ordinal.natCast_lt_omega0 t).trans_le hdom.1
    rw [hpi, hL]
    exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 R) htail hge
  have hpieps : Ordinal.omega0 ^ gamma < epsilonZero := by rw [← hpi]; exact hdom.2.2.1
  have hq := reserveStagePrincipalMultipleFacts gamma hpieps R
  have hs := actualFiniteTailClosureNorm (Ordinal.omega0 ^ gamma * (R : Ordinal)) hq.1 t
  rw [← hpi] at hq hs
  have hnorm : actualOrdinalNorm S = R * actualOrdinalNorm pi + t := by
    change actualOrdinalNorm (pi * (R : Ordinal) + (t : Ordinal)) = _
    rw [hs.2, hq.2]
  have hbudget : c + actualOrdinalNorm S < Phi t := by
    rw [hnorm]
    have hh := profileThreeMulLtPhi t
    omega
  have heL := normalRepresentationSound L
  have hell : (1 : Ordinal) < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [Ordinal.opow_one, ← hL]
    exact hlarge)
  have hlim : Order.IsSuccLimit L.1.repr := by
    rw [hL]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (zero_lt_one.trans hell))
  have hmax := actualMaximumPredecessor_correct L.1.repr hlim.bot_lt heL (Phi t-c)
  have hQnorm : actualOrdinalNorm Q = Phi t-c := actualLimitMaximumPredecessorSaturation _ heL hlim _
  have hle : actualOrdinalNorm S ≤ Phi t-c := by omega
  exact ⟨hsmall, hsmall.trans heL, hnorm, hbudget,
    hmax.2 ⟨hsmall, hle⟩, hle.trans_eq hQnorm.symm⟩

end LogicLineages.OrdinalComparison
