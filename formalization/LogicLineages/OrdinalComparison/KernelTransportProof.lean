module
public import LogicLineages.OrdinalComparison.KernelTransportTargets
public import LogicLineages.OrdinalComparison.SuffixKernelMonotoneProof
public import LogicLineages.OrdinalComparison.ReserveStageProof
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualControlledExitNormMonotone : Targets.ActualControlledExitNormMonotone := by
  intro g hmono hexp A B hAB he hnorm
  have hA := hAB.trans_lt he
  have hc := actualControlledCountsJointMonotone g g (fun _ => le_rfl) hmono A B hAB he hnorm
  rw [actualControlledNormIteration g A hA _ le_rfl,
    actualControlledNormIteration g B he _ le_rfl]
  exact ((hmono.iterate _ ) hnorm).trans ((iterate_index_mono hexp (actualOrdinalNorm B)) hc)

private theorem kernel_limitPart_tail (pi : Ordinal) (hl : Order.IsSuccLimit pi) (n : Nat) :
    actualLimitPart (pi + (n : Ordinal)) = pi := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualSuffixKernelFirstMaximum : Targets.ActualSuffixKernelFirstMaximum := by
  intro beta hb he c t ht
  dsimp only
  let pi := Ordinal.omega0 ^ beta
  let I := actualSuffixKernelInitial pi c t
  let Q := actualMaximumPredecessor pi (Phi t - c)
  let g := compensatedPrefixControl c
  have hin := actualSuffixKernelInput beta hb he c t ht
  have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hstep : actualControlledStep g I = Q := by
    change actualMaximumPredecessor (actualLimitPart I) (Phi (c + actualOrdinalNorm I) - c) = Q
    rw [hin.2.2]
    change actualMaximumPredecessor (actualLimitPart (pi + ((t-c-actualOrdinalNorm pi : Nat) : Ordinal))) (Phi t-c) = Q
    rw [kernel_limitPart_tail _ hl]
  have hQeps : Q < epsilonZero :=
    (actualMaximumPredecessor_correct pi hl.bot_lt he (Phi t-c)).1.1.trans he
  have hQnorm : actualOrdinalNorm Q = Phi t-c :=
    actualLimitMaximumPredecessorSaturation pi he hl (Phi t-c)
  have hc := (actualControlledCountRecursion g I hin.1).2 hin.2.1
  rw [hstep] at hc
  have hcount : actualSuffixKernelCount pi c t = actualControlledCount g Q + 1 := hc
  refine ⟨hstep, hcount, ?_⟩
  unfold actualSuffixKernel
  rw [hcount, Function.iterate_succ_apply]
  have hn := actualControlledNormIteration g Q hQeps (actualControlledCount g Q) le_rfl
  have hi := reserveCompensatedIteration c (actualOrdinalNorm Q) (actualControlledCount g Q)
  have hsum : c + actualOrdinalNorm Q = Phi t := by
    rw [hQnorm]
    have hh := self_lt_Phi t
    omega
  rw [hsum] at hi
  rw [hn]
  exact hi.symm

theorem actualSuffixKernelBelowFixedHead : Targets.ActualSuffixKernelBelowFixedHead := by
  intro beta hb he c t ht
  let pi := Ordinal.omega0 ^ beta
  have hmono := actualSuffixKernelInputMassMonotone beta hb he 0 c t (actualOrdinalNorm pi + t)
    (Nat.zero_le _) (Nat.le_add_left _ _) ht (by omega)
  have hi := actualFiniteTailClosureNorm pi he t
  have hzero : compensatedPrefixControl 0 = Phi := by funext n; simp [compensatedPrefixControl]
  have hinit : actualSuffixKernelInitial pi 0 (actualOrdinalNorm pi+t) = pi+(t:Ordinal) := by
    simp [actualSuffixKernelInitial]
  have hk : actualSuffixKernel pi 0 (actualOrdinalNorm pi+t) = actualTerminalValue (pi+(t:Ordinal)) := by
    unfold actualSuffixKernel actualSuffixKernelCount
    rw [hzero, hinit, actualControlledCountPhiAgreement _ hi.1]
    have hv := (actualTerminalValueIdentities (pi+(t:Ordinal)) hi.1).2
    rw [hi.2] at hv
    exact hv.symm
  rw [hk] at hmono
  exact hmono.trans (by rw [(actualTerminalValueIdentities _ hi.1).1]; exact Nat.le_add_right _ _)

end LogicLineages.OrdinalComparison
