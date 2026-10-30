module
public import LogicLineages.OrdinalComparison.OmegaBlockSupplierTargets
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.HeadCompleteCountProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem omega_block_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, Ordinal.opow_zero, one_mul, Nat.zero_add, Nat.one_mul] using
    (actualFiniteMonomialFacts 0 n).2.1

theorem actualOmegaOmegaFacts : Targets.ActualOmegaOmegaFacts := by
  have homega : Ordinal.omega0 < epsilonZero := by
    simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
  have hnw : actualOrdinalNorm Ordinal.omega0 = 2 := by
    simpa only [Nat.cast_one, Ordinal.opow_one, mul_one, Nat.add_zero, Nat.mul_one] using
      (actualFiniteMonomialFacts 1 1).2.1
  have hblock := actualCNFBlock Ordinal.omega0 0 homega
    (Ordinal.opow_pos _ Ordinal.omega0_pos) ⟨1, by decide⟩
  have he : Ordinal.omega0 ^ Ordinal.omega0 < epsilonZero := by
    simpa only [PNat.mk_coe, Nat.cast_one, mul_one, add_zero] using hblock.1
  have hn := hblock.2.1
  simp only [PNat.mk_coe, Nat.cast_one, mul_one, add_zero] at hn
  change actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0) =
    1 * (1 + actualOrdinalNorm Ordinal.omega0) + actualOrdinalNorm 0 at hn
  have hnzero : actualOrdinalNorm (0 : Ordinal) = 0 := by
    simpa only [Nat.cast_zero] using omega_block_nat_norm 0
  rw [hnw, hnzero] at hn
  exact ⟨he, Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 Ordinal.omega0_ne_zero, hn⟩

theorem actualOmegaOmegaMaximum : Targets.ActualOmegaOmegaMaximum := by
  intro b hb
  have homega : Ordinal.omega0 < epsilonZero := by
    simpa only [Nat.cast_one, Ordinal.opow_one] using finiteOmegaPowerBelowEpsilonZero 1
  have hmax : actualMaximumPredecessor Ordinal.omega0 (b - 1) = ((b - 1 : Nat) : Ordinal) := by
    simpa only [Nat.zero_add, Nat.cast_one, mul_one, Nat.cast_zero, mul_zero, zero_add,
      Nat.mul_zero, Nat.sub_zero] using actualFiniteHeadMaximum 0 (b - 1) (by omega)
  have hr := actualLowerPowerGreedyRecurrence Ordinal.omega0 Ordinal.omega0_pos homega b (by omega)
  dsimp only at hr
  rw [hmax, omega_block_nat_norm, show 1 + (b - 1) = b by omega,
    Nat.div_self (by omega : 0 < b), Nat.mod_self] at hr
  have hfinite : ((b - 1 : Nat) : Ordinal) < epsilonZero := by
    simpa only [Nat.cast_zero, Ordinal.opow_zero, one_mul] using (actualFiniteMonomialFacts 0 (b - 1)).1
  rw [actualOptimizedMaximumBaseCases.2.2 _ hfinite] at hr
  simpa only [actualLowerPowerMaximum, Nat.cast_one, mul_one, add_zero] using hr

private theorem omega_block_limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualOmegaBlockFirstStep : Targets.ActualOmegaBlockFirstStep := by
  intro c u hu
  dsimp only
  let g := compensatedPrefixControl c
  let a := actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)
  let B := Phi u
  let d := B - c - 1
  have hOmega := actualOmegaOmegaFacts
  have hi := actualHeadInputFacts _ hOmega.1 hOmega.2.1 (u - c) (by rw [hOmega.2.2]; omega)
  have hB : 3 ≤ B - c := by have h := self_lt_Phi u; dsimp [B]; omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hg : g (actualOrdinalNorm a) = B - c := by
    rw [hi.2.2]
    change Phi (c + (u - c)) - c = B - c
    rw [Nat.add_sub_of_le (by omega : c ≤ u)]
  have hstep : actualControlledStep g a = Ordinal.omega0 ^ (d : Ordinal) := by
    change actualMaximumPredecessor (actualLimitPart a) (g (actualOrdinalNorm a)) = _
    rw [show actualLimitPart a = Ordinal.omega0 ^ Ordinal.omega0 from
      omega_block_limitPart_tail _ hOmega.2.1 _, hg]
    exact actualOmegaOmegaMaximum _ hB
  have hn := actualControlledStepNorm g a hi.2.1 hi.1
  rw [hg] at hn
  have hc := (actualControlledCountRecursion g a hi.1).2 hi.2.1
  rw [hstep] at hc
  exact ⟨hd, hstep, hn, hc⟩

end LogicLineages.OrdinalComparison
