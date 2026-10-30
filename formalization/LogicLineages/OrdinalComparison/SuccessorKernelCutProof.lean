module
public import LogicLineages.OrdinalComparison.SuccessorKernelCutTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelMaximumProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualCompensatedControlComposition : Targets.ActualCompensatedControlComposition := by
  intro c w
  funext n
  simp only [prefixRemainderControl, compensatedPrefixControl, Nat.sub_sub, Nat.add_assoc]

private theorem cut_limitPart_tail (k : Ordinal) (hlim : Order.IsSuccLimit k) (n : Nat) :
    actualLimitPart (k + (n : Ordinal)) = k := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlim.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

private theorem cut_first (beta : Ordinal) (hb : 0 < beta)
    (he : Ordinal.omega0 ^ beta < epsilonZero) (a t : Nat)
    (ht : a + actualOrdinalNorm (Ordinal.omega0 ^ beta) ≤ t) :
    actualControlledStateAfter (compensatedPrefixControl a)
      (actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t) 1 =
      actualMaximumPredecessor (Ordinal.omega0 ^ beta) (Phi t - a) := by
  have hn := (actualSuffixKernelInput beta hb he a t ht).2.2
  have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  change actualMaximumPredecessor
    (actualLimitPart (actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t))
    (Phi (a + actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ beta) a t)) - a) = _
  rw [hn]
  unfold actualSuffixKernelInitial
  rw [cut_limitPart_tail _ hl]

theorem actualSuccessorKernelFirstStep : Targets.ActualSuccessorKernelFirstStep := by
  intro gamma hg he c t
  dsimp only
  intro ht
  have hL : Ordinal.omega0 ^ (gamma + 1) = Ordinal.omega0 ^ gamma * Ordinal.omega0 :=
    Ordinal.opow_add_one _ _
  have hgp : 0 < gamma + 1 := (lt_add_one gamma).trans_le' (le_of_lt hg)
  have he' : Ordinal.omega0 ^ (gamma + 1) < epsilonZero := by rw [hL]; exact he
  have ho := cut_first (gamma + 1) hgp he' c t (by rw [hL]; omega)
  have hi := cut_first (gamma + 1) hgp he' (c + actualOrdinalNorm (Ordinal.omega0 ^ gamma)) t
    (by rw [hL]; exact ht)
  rw [hL] at ho hi
  rw [ho, hi]
  have hPhi := self_lt_Phi t
  have hb : actualOrdinalNorm (Ordinal.omega0 ^ gamma) ≤ Phi t - c := by omega
  simpa only [Nat.sub_sub] using actualSuccessorPrincipalMaximumShift gamma hg he (Phi t - c) hb

private theorem cut_after_first (g : Nat → Nat) (I : Ordinal) (j : Nat) :
    actualControlledStateAfter g I (j + 1) =
      actualControlledStateAfter g (actualControlledStateAfter g I 1) j :=
  Function.iterate_succ_apply _ _ _

private theorem cut_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.zero_add] using actualFiniteHeadNorm 0 n

theorem actualSuccessorKernelCut : Targets.ActualSuccessorKernelCut := by
  intro gamma hg he c t
  dsimp only
  intro ht
  let theta := Ordinal.omega0 ^ gamma
  let L := theta * Ordinal.omega0
  let w := actualOrdinalNorm theta
  let h := compensatedPrefixControl c
  let g := compensatedPrefixControl (c + w)
  let I := actualSuffixKernelInitial L c t
  let J := actualSuffixKernelInitial L (c + w) t
  let E := actualSuffixKernelCount L (c + w) t
  let K := actualSuffixKernel L (c + w) t
  let outer := actualControlledStateAfter h I
  let inner := actualControlledStateAfter g J
  let r := inner 1
  change c + w + actualOrdinalNorm L ≤ t at ht
  have hL : Ordinal.omega0 ^ (gamma + 1) = L := Ordinal.opow_add_one _ _
  have hgp : 0 < gamma + 1 := (lt_add_one gamma).trans_le' (le_of_lt hg)
  have he' : Ordinal.omega0 ^ (gamma + 1) < epsilonZero := by rw [hL]; exact he
  have hin : J < epsilonZero ∧ Ordinal.omega0 ≤ J ∧ c + w + actualOrdinalNorm J = t := by
    simpa only [hL] using actualSuffixKernelInput (gamma + 1) hgp he' (c + w) t (by rw [hL]; exact ht)
  have hout := actualSuffixKernelInput (gamma + 1) hgp he' c t (by rw [hL]; change c + actualOrdinalNorm L ≤ t; omega)
  rw [hL] at hout
  have htr := actualSuffixKernelTrace (gamma + 1) hgp he' (c + w) t (by rw [hL]; exact ht)
  rw [hL] at htr
  have hE : 0 < E := htr.1
  have hfirst : outer 1 = theta + r := actualSuccessorKernelFirstStep gamma hg he c t ht
  have hrmax : r = actualMaximumPredecessor L (Phi t - (c + w)) := by
    simpa only [hL] using cut_first (gamma + 1) hgp he' (c + w) t (by rw [hL]; exact ht)
  have htheta : theta < epsilonZero := (Ordinal.le_mul_left _ Ordinal.omega0_pos).trans_lt he
  have hthetaPos : 0 < theta := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hLPos : 0 < L := mul_pos hthetaPos Ordinal.omega0_pos
  have hrL : r < L := by
    rw [hrmax]
    exact (actualMaximumPredecessor_correct L hLPos he _).1.1
  have hr : r < epsilonZero := hrL.trans he
  have hmin : actualMinExponentAtLeast theta gamma :=
    (actualMinExponentDivisibility theta htheta gamma).mpr (dvd_refl theta)
  have hb : ∀ n : Nat, w ≤ h (w + n) := by
    intro n
    have hh := (compensatedPrefixControlBounds c).2 (w + n)
    change w ≤ compensatedPrefixControl c (w + n)
    omega
  have hp := actualPrefixControlTrace h theta r htheta hr gamma hg hmin (by rw [hL]; exact hrL) hb
  dsimp only at hp
  rw [actualCompensatedControlComposition] at hp
  have hc : E = actualControlledCount g r + 1 :=
    (actualControlledCountRecursion g J hin.1).2 hin.2.1
  have htrace : ∀ i : Nat, 1 ≤ i → i ≤ E → outer i = theta + inner i := by
    intro i hi hiE
    have hj : i - 1 ≤ actualControlledCount g r := by omega
    have hx := hp.1 (i - 1) hj
    change actualControlledStateAfter h (theta + r) (i - 1) =
      theta + actualControlledStateAfter g r (i - 1) at hx
    change actualControlledStateAfter h I i = theta + actualControlledStateAfter g J i
    rw [show i = (i - 1) + 1 by omega, cut_after_first, cut_after_first]
    change actualControlledStateAfter h (outer 1) (i - 1) =
      theta + actualControlledStateAfter g r (i - 1)
    rw [hfirst]
    exact hx
  have hK : c + w ≤ K := by
    have hn := htr.2.1 E le_rfl
    change c + w + actualOrdinalNorm (inner E) = K at hn
    omega
  have houtertr := actualControlledTraceFirstFinite h I hout.1
  have houterpos : 0 < actualControlledCount h I := by
    by_contra hzero
    have hz : actualControlledCount h I = 0 := by omega
    have hf := houtertr.1
    rw [hz, actualControlledStateAfter_zero] at hf
    exact not_lt_of_ge hout.2.1 hf
  have hle : E ≤ actualControlledCount h I := by
    by_contra hn
    have hcE : actualControlledCount h I < E := by omega
    have hx := htrace (actualControlledCount h I) houterpos (le_of_lt hcE)
    have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hg)
    have hnon : Ordinal.omega0 ≤ theta := Ordinal.omega0_le_of_isSuccLimit hlim
    have hf : outer (actualControlledCount h I) < Ordinal.omega0 := houtertr.1
    rw [hx] at hf
    exact not_lt_of_ge (hnon.trans le_self_add) hf
  refine ⟨htrace, hK, hle, ?_⟩
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp htr.2.2.1
  have hn' : inner E = (n : Ordinal) := hn
  have hnorm := htr.2.1 E le_rfl
  change c + w + actualOrdinalNorm (inner E) = K at hnorm
  rw [hn', cut_nat_norm] at hnorm
  have htail : K - c - w = n := by omega
  change outer E = theta + ((K - c - w : Nat) : Ordinal)
  rw [htrace E hE le_rfl, hn', htail]

end LogicLineages.OrdinalComparison
