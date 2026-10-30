module
public import LogicLineages.OrdinalComparison.GrowingBudgetCutProof
public import LogicLineages.OrdinalComparison.NumericalFixedBudgetProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem transfer_limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

private theorem partition_input_congruence (d m : Nat) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (b B : Nat) (hmod : Nat.ModEq (restrictedPartitionPeriod d m) b B) :
    Nat.ModEq m (restrictedPartitionCount d b) (restrictedPartitionCount d B) := by
  rcases le_total b B with hle | hle
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    rw [hk]
    exact (restrictedPartitionPeriodMultiple d m b k hd hm).symm
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    rw [hk]
    exact restrictedPartitionPeriodMultiple d m B k hd hm

theorem actualNumericalCongruentBudgetTransfer : Targets.ActualNumericalCongruentBudgetTransfer := by
  intro d m c S n hd hm hcS h
  dsimp only
  let g := fun i : Nat => h i - c
  let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
  intro hlive
  have hpow := finiteOmegaPowerBelowEpsilonZero d
  have hdpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ (d : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hdpos)
  have hae : a < epsilonZero := (actualFiniteTailClosureNorm _ hpow n).1
  have hanon : Ordinal.omega0 ≤ a := (Ordinal.omega0_le_of_isSuccLimit hlim).trans le_self_add
  have hnormpow : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d + 1 := by
    simpa only [Nat.cast_one, mul_one, Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1
  have hanorm : actualOrdinalNorm a = d + 1 + n := by
    rw [(actualFiniteTailClosureNorm _ hpow n).2, hnormpow]
  let z := actualControlledStep (fun _ => g 0) a
  let B := g 0
  have hrec := (actualScheduledCountRecursion g a hae).2 hanon
  have hpos : 0 < actualScheduledCount g a := by omega
  have hfirst := hlive 0 hpos
  change c + actualOrdinalNorm a ≤ h 0 ∧ Nat.ModEq (restrictedPartitionPeriod d m) (h 0) S at hfirst
  have hB : actualOrdinalNorm a ≤ B := by dsimp [B, g]; omega
  have hBmod : Nat.ModEq (restrictedPartitionPeriod d m) B (S - c) :=
    Nat.ModEq.sub_right (by omega : c ≤ h 0) hcS hfirst.2
  have hznorm : actualOrdinalNorm z = B := actualControlledStepNorm (fun _ => g 0) a hanon hae
  have hzbound : z < Ordinal.omega0 ^ (d : Ordinal) := by
    have hz := (actualMaximumPredecessor_correct _ hlim.bot_lt hpow B).1.1
    change actualMaximumPredecessor (actualLimitPart a) B < _
    rw [transfer_limitPart_tail _ hlim n]
    exact hz
  have hchild : ∀ i : Nat, i < actualScheduledCount (fun j => g (j + 1)) z →
      actualOrdinalNorm (actualScheduledStateAfter (fun j => g (j + 1)) z i) ≤ g (i + 1) ∧
        Nat.ModEq (restrictedPartitionPeriod d m) (g (i + 1)) B := by
    intro i hi
    have hidx : i + 1 < actualScheduledCount g a := by rw [hrec]; exact Nat.succ_lt_succ hi
    have hbi := hlive (i + 1) hidx
    change c + actualOrdinalNorm (actualScheduledStateAfter (fun j => g (j + 1)) z i) ≤ h (i + 1) ∧
      Nat.ModEq (restrictedPartitionPeriod d m) (h (i + 1)) S at hbi
    have hsub := Nat.ModEq.sub_right (by omega : c ≤ h (i + 1)) hcS hbi.2
    refine ⟨?_, hsub.trans hBmod.symm⟩
    change actualOrdinalNorm (actualScheduledStateAfter (fun j => g (j + 1)) z i) ≤ h (i + 1) - c
    omega
  have hchildmod := actualGrowingBudgetCutTransfer d m hd hm (fun j => g (j + 1)) z
    hzbound B (by rw [hznorm]) hchild
  have hconst := (actualControlledCountRecursion (fun _ => B) a hae).2 hanon
  have hsame : Nat.ModEq m (actualScheduledCount g a) (actualControlledCount (fun _ => B) a) := by
    rw [hrec, hconst]
    exact hchildmod.add (Nat.ModEq.refl 1)
  have hfixed := actualNumericalFixedBudgetPartitionCount d 0 B n hd (by omega) (by
    simpa only [Nat.zero_add, a] using hB)
  simp only [Nat.zero_add, Nat.sub_zero] at hfixed
  rw [hfixed] at hsame
  exact hsame.trans (partition_input_congruence d m hd hm B (S - c) hBmod)

end LogicLineages.OrdinalComparison
