module
public import LogicLineages.OrdinalComparison.ThetaEntryTargets
public import LogicLineages.OrdinalComparison.OmegaBlockPrefixProof
public import LogicLineages.OrdinalComparison.HeadEndpointProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem theta_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, Ordinal.opow_zero, one_mul, Nat.zero_add, Nat.one_mul] using
    (actualFiniteMonomialFacts 0 n).2.1

private theorem theta_zero_norm : actualOrdinalNorm (0 : Ordinal) = 0 := by
  simpa only [Nat.cast_zero] using theta_nat_norm 0

private theorem theta_omega_norm : actualOrdinalNorm Ordinal.omega0 = 2 := by
  simpa only [Nat.cast_one, Ordinal.opow_one, mul_one, Nat.mul_one] using
    (actualFiniteMonomialFacts 1 1).2.1

private theorem theta_omega_below : Ordinal.omega0 < epsilonZero := by
  simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1

theorem actualOmegaMultipleFacts : Targets.ActualOmegaMultipleFacts := by
  intro q
  by_cases hq : q = 0
  · subst q
    simp only [Nat.cast_zero, mul_zero, Nat.mul_zero]
    have hz : (0 : Ordinal) < epsilonZero := by
      simpa only [Nat.cast_zero, Ordinal.opow_zero, one_mul] using (actualFiniteMonomialFacts 0 0).1
    refine ⟨hz, theta_zero_norm, ?_⟩
    exact (actualMinExponentDivisibility 0 hz Ordinal.omega0).mpr (dvd_zero _)
  · have hb := actualCNFBlock Ordinal.omega0 0 theta_omega_below
      (Ordinal.opow_pos _ Ordinal.omega0_pos) ⟨q, Nat.pos_of_ne_zero hq⟩
    have he : Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) < epsilonZero := by
      simpa only [PNat.mk_coe, add_zero] using hb.1
    have hn : actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal)) = 3 * q := by
      have h := hb.2.1
      simp only [PNat.mk_coe, add_zero, theta_zero_norm, theta_omega_norm] at h
      simpa only [Nat.add_zero, Nat.mul_comm] using h
    exact ⟨he, hn, (actualMinExponentDivisibility _ he _).mpr (dvd_mul_right _ _)⟩

theorem actualThetaFacts : Targets.ActualThetaFacts := by
  have he := (actualFiniteTailClosureNorm Ordinal.omega0 theta_omega_below 1).1
  simp only [Nat.cast_one] at he
  have hn : actualOrdinalNorm (Ordinal.omega0 + 1) = 3 := by
    simpa only [Nat.cast_one, theta_omega_norm] using
      (actualFiniteTailClosureNorm Ordinal.omega0 theta_omega_below 1).2
  have hb := actualCNFBlock (Ordinal.omega0 + 1) 0 he
    (Ordinal.opow_pos _ Ordinal.omega0_pos) ⟨1, by decide⟩
  have hTheta : Ordinal.omega0 ^ (Ordinal.omega0 + 1) < epsilonZero := by
    simpa only [PNat.mk_coe, Nat.cast_one, mul_one, add_zero] using hb.1
  have hnorm : actualOrdinalNorm (Ordinal.omega0 ^ (Ordinal.omega0 + 1)) = 4 := by
    simpa only [PNat.mk_coe, Nat.cast_one, mul_one, add_zero, hn, theta_zero_norm] using hb.2.1
  refine ⟨hTheta, ?_, hnorm⟩
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    (ne_of_gt (Ordinal.omega0_pos.trans_le le_self_add))

private theorem omega_budget_one :
    actualMaximumPredecessor (Ordinal.omega0 ^ Ordinal.omega0) 1 = 1 := by
  symm
  apply actualMaximumPredecessor_unique _ actualOmegaOmegaFacts.2.1.bot_lt actualOmegaOmegaFacts.1 1 1
  constructor
  · constructor
    · exact Ordinal.one_lt_omega0.trans_le (Ordinal.omega0_le_of_isSuccLimit actualOmegaOmegaFacts.2.1)
    · have h := theta_nat_norm 1
      simpa only [Nat.cast_one] using h.le
  · intro x hx
    by_cases hf : x < Ordinal.omega0
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hf
      have hnorm := hx.2
      rw [hn, theta_nat_norm] at hnorm
      rw [hn]
      exact_mod_cast hnorm
    · have hnorm := actualNonfiniteNormLowerBound x (hx.1.trans actualOmegaOmegaFacts.1) (le_of_not_gt hf)
      have hbudget : actualOrdinalNorm x ≤ 1 := hx.2
      omega

theorem actualThetaBudgetMaximum : Targets.ActualThetaBudgetMaximum := by
  intro u hu hmod
  have he := (actualFiniteTailClosureNorm Ordinal.omega0 theta_omega_below 1).1
  simp only [Nat.cast_one] at he
  have htop : actualMaximumPredecessor (Ordinal.omega0 + 1) (u - 1) = Ordinal.omega0 := by
    symm
    apply actualMaximumPredecessor_unique _
      (Ordinal.omega0_pos.trans_le le_self_add) he (u - 1) Ordinal.omega0
    refine ⟨⟨Order.lt_add_one_iff.mpr le_rfl, ?_⟩, ?_⟩
    · rw [theta_omega_norm]
      omega
    · intro x hx
      exact Order.lt_add_one_iff.mp hx.1
  have hrem : u % 3 = 1 := by change u % 3 = 1 at hmod; exact hmod
  have hquot : u / 3 = (u - 1) / 3 := by omega
  have hr := actualLowerPowerGreedyRecurrence (Ordinal.omega0 + 1)
    (Ordinal.omega0_pos.trans_le le_self_add) he u (by omega)
  dsimp only at hr
  rw [htop, theta_omega_norm, show 1 + 2 = 3 from rfl, hrem] at hr
  change actualMaximumPredecessor (Ordinal.omega0 ^ (Ordinal.omega0 + 1)) u =
    Ordinal.omega0 ^ Ordinal.omega0 * ((u / 3 : Nat) : Ordinal) +
      actualMaximumPredecessor (Ordinal.omega0 ^ Ordinal.omega0) 1 at hr
  rw [omega_budget_one, hquot] at hr
  exact hr

end LogicLineages.OrdinalComparison
