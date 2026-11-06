module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSupplierTargets
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of KernelCounterCalibrationProof.degree_norm / actualFiniteKernelInput and CounterSourceTheoremStartupProof. The finite-domain statements and proof steps are unchanged; only the namespace and frozen supplier alias are changed. -/

private theorem degree_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d + 1 := by
  simpa only [Nat.cast_one, mul_one, Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1

theorem actualFiniteKernelInput : FocusedSupplierTargets.FiniteKernelInput := by
  intro d c t hd ht
  have hpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hin := actualSuffixKernelInput (d : Ordinal) hpos (finiteOmegaPowerBelowEpsilonZero d)
    c t (by rw [degree_norm]; omega)
  exact ⟨degree_norm d, hin.1, hin.2.2, (by have := self_lt_Phi t; omega)⟩

open CounterLeaderExpansion

private theorem limitPart_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

theorem actualKernelStartup : FocusedSupplierTargets.KernelStartup := by
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

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
