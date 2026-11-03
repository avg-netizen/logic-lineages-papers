module
public import LogicLineages.OrdinalComparison.WholeScheduledCountRecursionProof
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WholeScheduledCount.Proof

theorem uniformLinearLowerBound : Targets.UniformLinearLowerBound := by
  intro q
  induction q with
  | zero => intro b a _ _ _; exact Nat.zero_le _
  | succ q ih =>
    intro b a hqa ha hb
    have hqcast : (0 : Ordinal) < ((q+1 : Nat) : Ordinal) := by
      exact_mod_cast Nat.succ_pos q
    have hlim := Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hqcast
    have hn : Ordinal.omega0 ≤ a :=
      (Ordinal.omega0_le_of_isSuccLimit hlim).trans hqa
    have hlt : Ordinal.omega0 * (q : Ordinal) < a := by
      have hq : (q : Ordinal) < ((q+1 : Nat) : Ordinal) := by exact_mod_cast Nat.lt_succ_self q
      exact (mul_lt_mul_of_pos_left hq Ordinal.omega0_pos) |>.trans_le hqa
    have hnorm : actualOrdinalNorm (Ordinal.omega0 * (q : Ordinal)) = 2*q := by
      simpa only [Nat.cast_one,Ordinal.opow_one] using (actualFiniteMonomialFacts 1 q).2.1
    have hm := actualMaximumPredecessor_correct a (Ordinal.omega0_pos.trans_le hn) ha (b 0)
    have hpred : Ordinal.omega0 * (q : Ordinal) ≤ actualMaximumPredecessor a (b 0) := by
      apply hm.2
      refine ⟨hlt,?_⟩
      rw [hnorm]
      have := hb 0
      omega
    have hi := ih (fun i => b (i+1)) (actualMaximumPredecessor a (b 0))
      hpred (hm.1.1.trans ha) (by intro i; have := hb (i+1); omega)
    rw [(exactRecursion b a ha).2 hn]
    omega
end LogicLineages.OrdinalComparison.WholeScheduledCount.Proof
