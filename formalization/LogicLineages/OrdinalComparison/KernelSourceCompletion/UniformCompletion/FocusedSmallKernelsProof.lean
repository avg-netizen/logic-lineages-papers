module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedControlProof
public import LogicLineages.OrdinalComparison.SmallKernelSuppliersProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixMaximumProof
public import Mathlib.Order.Iterate

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of SmallKernelsProof excluding its linked-residue parity dependency. The exact small-kernel proofs use the direct focused parity theorem instead. -/

private theorem kernel_omega_norm : actualOrdinalNorm Ordinal.omega0 = 2 := by
  simpa only [Nat.cast_one, mul_one, Nat.cast_zero, add_zero, Nat.mul_one, Nat.add_zero] using
    actualFiniteHeadNorm 1 0

private theorem kernel_square_norm : actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)) = 3 := by
  simpa only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_one] using
    (actualFiniteMonomialFacts 2 1).2.1

private theorem kernel_limitPart_tail (lam : Ordinal) (hlam : Order.IsSuccLimit lam) (n : Nat) :
    actualLimitPart (lam + (n : Ordinal)) = lam := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlam.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualOmegaSuffixKernel : FocusedSupplierTargets.OmegaSuffixKernel := by
  intro a t ht
  have hg : ∀ n : Nat, n ≤ compensatedPrefixControl a n :=
    fun n => ((compensatedPrefixControlBounds a).2 n).2.le
  have hE : actualSuffixKernelCount Ordinal.omega0 a t = 1 := by
    unfold actualSuffixKernelCount actualSuffixKernelInitial
    rw [kernel_omega_norm]
    simpa only [Nat.cast_one, mul_one] using actualExpansiveControlLinearCount
      (compensatedPrefixControl a) hg 1 (t - a - 2)
  refine ⟨hE, ?_⟩
  unfold actualSuffixKernel
  rw [hE]
  rfl

theorem actualOmegaSquaredSuffixCount : FocusedSupplierTargets.OmegaSquaredSuffixCount := by
  intro a t ht
  let pi := Ordinal.omega0 ^ (2 : Ordinal)
  let I := actualSuffixKernelInitial pi a t
  let g := compensatedPrefixControl a
  have he : pi < epsilonZero := finiteOmegaPowerBelowEpsilonZero 2
  have hn : actualOrdinalNorm pi = 3 := kernel_square_norm
  have hdom : a + actualOrdinalNorm pi ≤ t := by rw [hn]; exact ht
  have hi := actualSuffixKernelInput (2 : Ordinal) (by norm_num) he a t hdom
  have hnorm : actualOrdinalNorm I = t - a := by have h := hi.2.2; change a + actualOrdinalNorm I = t at h; omega
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
    change actualMaximumPredecessor (actualLimitPart (pi + ((t - a - actualOrdinalNorm pi : Nat) : Ordinal)))
      (Phi (a + (t - a)) - a) = _
    rw [kernel_limitPart_tail pi hlim, Nat.add_sub_of_le ha, actualOmegaSquaredMaximum _ hb]
  have hg : ∀ n : Nat, n ≤ g n := fun n => ((compensatedPrefixControlBounds a).2 n).2.le
  change actualControlledCount g I = _
  rw [(actualControlledCountRecursion g I hi.1).2 hi.2.1, hstep,
    actualExpansiveControlLinearCount g hg]
  have hm : Phi t % 2 = 0 := Nat.even_iff.mp (actualPhiEven t)
  omega

theorem actualOmegaSquaredMassClasses : FocusedSupplierTargets.OmegaSquaredMassClasses := by
  intro a b t ha hb
  unfold actualSuffixKernel
  rw [actualOmegaSquaredSuffixCount a t ha, actualOmegaSquaredSuffixCount b t hb]
  have hmono : StrictMono (fun n : Nat => (Phi^[n]) t) :=
    Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi t)
  have hPhi := self_lt_Phi t
  constructor
  · rw [hmono.injective.eq_iff]
    omega
  · rw [hmono.lt_iff_lt]
    omega

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
