module
public import LogicLineages.OrdinalComparison.GrowingBudgetTransferTargets
public import LogicLineages.OrdinalComparison.ScheduledCountProof
public import LogicLineages.OrdinalComparison.ConstantCutPeriodProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem constant_count_period_multiple (d m : Nat) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (a : Ordinal) (ha : a < Ordinal.omega0 ^ (d : Ordinal)) (b : Nat)
    (hb : actualOrdinalNorm a ≤ b) (k : Nat) :
    Nat.ModEq m (actualControlledCount (fun _ => b + restrictedPartitionPeriod d m * k) a)
      (actualControlledCount (fun _ => b) a) := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.ModEq.refl _
  | succ k ih =>
    have hs := actualConstantBudgetCutPeriod d m hd hm a ha
      (b + restrictedPartitionPeriod d m * k) (by omega)
    simpa only [Nat.mul_succ, Nat.add_assoc] using hs.trans ih

theorem actualConstantBudgetCutCongruence : Targets.ActualConstantBudgetCutCongruence := by
  intro d m hd hm a ha b B hb hB hmod
  rcases le_total b B with hle | hle
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod
    rw [hk]
    exact (constant_count_period_multiple d m hd hm a ha b hb k).symm
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    rw [hk]
    exact constant_count_period_multiple d m hd hm a ha B hB k

theorem actualGrowingBudgetCutTransfer : Targets.ActualGrowingBudgetCutTransfer := by
  intro d m hd hm budget a
  induction a using Ordinal.lt_wf.induction generalizing budget with
  | h a ih =>
    intro ha B hB hlive
    have hae : a < epsilonZero := ha.trans (finiteOmegaPowerBelowEpsilonZero d)
    by_cases hf : a < Ordinal.omega0
    · rw [(actualScheduledCountRecursion budget a hae).1 hf,
        (actualControlledCountRecursion (fun _ => B) a hae).1 hf]
    · have hn := le_of_not_gt hf
      let z := actualControlledStep (fun _ => budget 0) a
      have hzlt : z < a := actualControlledStepStrict (fun _ => budget 0) a hn hae
      have hze : z < epsilonZero := hzlt.trans hae
      have hzbound : z < Ordinal.omega0 ^ (d : Ordinal) := hzlt.trans ha
      have hznorm : actualOrdinalNorm z = budget 0 := actualControlledStepNorm (fun _ => budget 0) a hn hae
      have hc := (actualScheduledCountRecursion budget a hae).2 hn
      have hpos : 0 < actualScheduledCount budget a := by omega
      have hfirst := hlive 0 hpos
      change actualOrdinalNorm a ≤ budget 0 ∧
        Nat.ModEq (restrictedPartitionPeriod d m) (budget 0) B at hfirst
      have hchild : ∀ i : Nat, i < actualScheduledCount (fun j => budget (j + 1)) z →
          actualOrdinalNorm (actualScheduledStateAfter (fun j => budget (j + 1)) z i) ≤ budget (i + 1) ∧
          Nat.ModEq (restrictedPartitionPeriod d m) (budget (i + 1)) (budget 0) := by
        intro i hi
        have hidx : i + 1 < actualScheduledCount budget a := by rw [hc]; exact Nat.succ_lt_succ hi
        have hbi := hlive (i + 1) hidx
        change actualOrdinalNorm (actualScheduledStateAfter (fun j => budget (j + 1)) z i) ≤ budget (i + 1) ∧
          Nat.ModEq (restrictedPartitionPeriod d m) (budget (i + 1)) B at hbi
        exact ⟨hbi.1, hbi.2.trans hfirst.2.symm⟩
      have hchildmod := ih z hzlt (fun j => budget (j + 1)) hzbound (budget 0) (by rw [hznorm]) hchild
      have hconstant := (actualControlledCountRecursion (fun _ => budget 0) a hae).2 hn
      have hsame : Nat.ModEq m (actualScheduledCount budget a)
          (actualControlledCount (fun _ => budget 0) a) := by
        rw [hc, hconstant]
        exact hchildmod.add (Nat.ModEq.refl 1)
      exact hsame.trans (actualConstantBudgetCutCongruence d m hd hm a ha (budget 0) B
        hfirst.1 hB hfirst.2)

end LogicLineages.OrdinalComparison
