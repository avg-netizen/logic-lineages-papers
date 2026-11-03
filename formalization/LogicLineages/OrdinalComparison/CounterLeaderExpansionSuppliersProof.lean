module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionTargets
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionTargets
public import LogicLineages.OrdinalComparison.SmallKernelsTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelsProof
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixMaximumProof
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Algebra.Ring.Parity

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof

/-! The three exact unsigned supplier contracts used by the counter-leader
expansion. These reproduce the original domains without importing the signed
kernel or linked residue developments. -/

private theorem power_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
  simpa only [Nat.cast_one,mul_one,Nat.mul_one] using
    (actualFiniteMonomialFacts d 1).2.1

private theorem next_power (n : Nat) :
    Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0 =
      Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal) := by
  rw [← Ordinal.opow_add_one]
  congr 1

theorem block : LogicLineages.OrdinalComparison.Targets.ActualFiniteKernelBlockRecursion := by
  intro n c t ht
  dsimp only
  have hpos : (0 : Ordinal) < ((n+1 : Nat) : Ordinal) := by
    exact_mod_cast (by omega : 0 < n+1)
  have heps : Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0 < epsilonZero := by
    rw [next_power]
    exact finiteOmegaPowerBelowEpsilonZero (n+2)
  have hn : actualOrdinalNorm
      (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0) = n+3 := by
    rw [next_power,power_norm]
  have hdom : c + actualOrdinalNorm (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)) +
      actualOrdinalNorm (Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0) ≤ t := by
    rw [power_norm,hn]
    omega
  have hc := actualSuccessorCountCocycle ((n+1 : Nat) : Ordinal) hpos heps c t hdom
  have hv := actualSuccessorKernelComposition ((n+1 : Nat) : Ordinal) hpos heps c t hdom
  rw [next_power,power_norm] at hc hv
  constructor
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv

private theorem control_power_of_two (j n : Nat) :
    ∃ k : Nat, fastControl j n = 2 ^ k := by
  induction j generalizing n with
  | zero => exact ⟨n, rfl⟩
  | succ j ih =>
    change ∃ k : Nat, (fastControl j)^[n + 1] n = 2 ^ k
    rw [Function.iterate_succ_apply']
    exact ih _

theorem phiEven : LogicLineages.OrdinalComparison.Targets.ActualPhiEven := by
  intro t
  obtain ⟨k, hk⟩ := control_power_of_two 5 (t + 100)
  have hlarge : 1 < fastControl 5 (t + 100) := by
    have h := self_lt_fastControl 5 (t + 100)
    omega
  have hn : k ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hk
    omega
  change Even (fastControl 5 (t + 100))
  rw [hk]
  exact even_two.pow_of_ne_zero hn

private theorem kernel_square_norm :
    actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)) = 3 := by
  simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
    (actualFiniteMonomialFacts 2 1).2.1

private theorem kernel_limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem quadraticCount : LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredSuffixCount := by
  intro a t ht
  let pi := Ordinal.omega0 ^ (2 : Ordinal)
  let I := actualSuffixKernelInitial pi a t
  let g := compensatedPrefixControl a
  have he : pi < epsilonZero := finiteOmegaPowerBelowEpsilonZero 2
  have hn : actualOrdinalNorm pi = 3 := kernel_square_norm
  have hdom : a + actualOrdinalNorm pi ≤ t := by rw [hn]; exact ht
  have hi := actualSuffixKernelInput (2 : Ordinal) (by norm_num) he a t hdom
  have hnorm : actualOrdinalNorm I = t - a := by
    have h := hi.2.2
    change a + actualOrdinalNorm I = t at h
    omega
  have ha : a ≤ t := by omega
  have hPhi := self_lt_Phi t
  have hb : 2 ≤ Phi t - a := by omega
  have hlim : Order.IsSuccLimit pi :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by norm_num)
  have hstep : actualControlledStep g I =
      Ordinal.omega0 * (((Phi t - a) / 2 : Nat) : Ordinal) +
        (((Phi t - a) % 2 : Nat) : Ordinal) := by
    unfold actualControlledStep
    rw [hnorm]
    change actualMaximumPredecessor
      (actualLimitPart (pi + ((t - a - actualOrdinalNorm pi : Nat) : Ordinal)))
      (Phi (a + (t - a)) - a) = _
    rw [kernel_limitPart_tail pi hlim, Nat.add_sub_of_le ha, actualOmegaSquaredMaximum _ hb]
  have hg : ∀ n : Nat, n ≤ g n := fun n => ((compensatedPrefixControlBounds a).2 n).2.le
  change actualControlledCount g I = _
  rw [(actualControlledCountRecursion g I hi.1).2 hi.2.1, hstep,
    actualExpansiveControlLinearCount g hg]
  have hm : Phi t % 2 = 0 := Nat.even_iff.mp (phiEven t)
  omega

end LogicLineages.OrdinalComparison.CounterLeaderExpansion.Proof
