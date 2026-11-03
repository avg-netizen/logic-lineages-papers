module
public import LogicLineages.OrdinalComparison.KernelReachableInputConventionTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelReachableInputConvention.Proof
attribute [local irreducible] Phi fastControl

theorem numerical_facts (t : Nat) (ht : 4 ≤ t) :
    1 < coefficient t ∧ firstBudget t % 2 = 1 ∧
    2*coefficient t+1 = firstBudget t ∧ 1+firstBudget t = Phi t := by
  have hg := self_lt_Phi t
  have he := Nat.even_iff.mp (CounterLeaderExpansion.Proof.phiEven t)
  unfold coefficient firstBudget
  omega

theorem limit_below (t : Nat) : limitState t < epsilonZero := by
  simpa only [limitState,Nat.cast_one,Ordinal.opow_one] using
    (actualFiniteMonomialFacts 1 (coefficient t)).1

theorem limit_norm (t : Nat) : actualOrdinalNorm (limitState t) = 2*coefficient t := by
  simpa only [limitState,Nat.cast_one,Ordinal.opow_one] using
    (actualFiniteMonomialFacts 1 (coefficient t)).2.1

theorem shared_norm (t : Nat) (ht : 4 ≤ t) :
    1+actualOrdinalNorm (sharedState t) = Phi t := by
  have hn := (actualFiniteTailClosureNorm (limitState t) (limit_below t) 1).2
  have hq := numerical_facts t ht
  simp only [Nat.cast_one] at hn
  unfold sharedState
  rw [hn,limit_norm]
  omega

theorem limit_tail (a : Ordinal) (ha : Order.IsSuccLimit a) (n : Nat) :
    actualLimitPart (a+(n : Ordinal)) = a := by
  obtain ⟨q,hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp ha.isSuccPrelimit
  unfold actualLimitPart
  rw [hq,Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n),add_zero]

theorem square_norm : actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)) = 3 := by
  simpa only [Nat.cast_ofNat,Nat.cast_one,mul_one,Nat.mul_one] using
    (actualFiniteMonomialFacts 2 1).2.1

theorem first_data (t : Nat) (ht : 4 ≤ t) : FirstData t := by
  have hq := numerical_facts t ht
  have hb : 2 ≤ firstBudget t := by omega
  have hm : actualMaximumPredecessor (Ordinal.omega0 ^ (2 : Ordinal))
      (firstBudget t) = sharedState t := by
    have h := actualOmegaSquaredMaximum (firstBudget t) hb
    rw [hq.2.1] at h
    simpa only [sharedState,limitState,coefficient,Nat.cast_one] using h
  have hp : (0 : Ordinal) < (2 : Ordinal) := by norm_num
  have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hp)
  have hin := actualSuffixKernelInput (2 : Ordinal) hp
    (finiteOmegaPowerBelowEpsilonZero 2) 1 t (by rw [square_norm]; omega)
  have hpart : actualLimitPart (initial t) = Ordinal.omega0 ^ (2 : Ordinal) := by
    exact limit_tail _ hl (t-1-actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)))
  have hstep : actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 1 = sharedState t := by
    change actualMaximumPredecessor (actualLimitPart (initial t))
      (Phi (1+actualOrdinalNorm (initial t))-1) = sharedState t
    rw [hpart]
    change actualMaximumPredecessor (Ordinal.omega0 ^ (2 : Ordinal))
      (Phi (1+actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) 1 t))-1) = _
    rw [hin.2.2]
    exact hm
  exact ⟨hq.1,hq.2.1,shared_norm t ht,hstep,hm⟩

theorem exactCommonFirstStep : Targets.ExactCommonFirstStep := by
  have hi : initial 4 = Ordinal.omega0 ^ (2 : Ordinal) := by
    simp only [initial,actualSuffixKernelInitial,square_norm]
    simp only [show (4-1-3 : Nat) = 0 from rfl,Nat.cast_zero,add_zero]
  exact ⟨hi,first_data 4 (by decide)⟩
end LogicLineages.OrdinalComparison.KernelReachableInputConvention.Proof
