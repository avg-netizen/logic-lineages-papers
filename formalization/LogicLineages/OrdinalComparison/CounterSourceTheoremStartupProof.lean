module
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof
open CounterLeaderExpansion

private theorem limitPart_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

theorem actualKernelStartup : Targets.ActualKernelStartup := by
  intro d c t hd ht
  dsimp only
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hn : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
    simpa only [Nat.cast_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1
  have hi := actualSuffixKernelInput (d : Ordinal) hp (finiteOmegaPowerBelowEpsilonZero d)
    c t (by rw [hn]; omega)
  have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  have hs : actualControlledStep (compensatedPrefixControl c)
      (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t) =
      actualMaximumPredecessor (Ordinal.omega0 ^ (d : Ordinal)) (Phi t-c) := by
    change actualMaximumPredecessor
      (actualLimitPart (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t))
      (Phi (c+actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t))-c) = _
    rw [hi.2.2]
    unfold actualSuffixKernelInitial
    rw [limitPart_tail _ hl]
  refine ⟨hi.2.2,hs,?_,rfl⟩
  have hc := (actualControlledCountRecursion (compensatedPrefixControl c)
    (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t) hi.1).2 hi.2.1
  rw [hs] at hc
  exact hc

end LogicLineages.OrdinalComparison.CounterSourceTheorem.Proof
