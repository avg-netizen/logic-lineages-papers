module
public import LogicLineages.OrdinalComparison.ControlSegmentTargets
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualControlledCountTraceDecomposition : Targets.ActualControlledCountTraceDecomposition := by
  intro g a ha i
  induction i with
  | zero =>
    intro _
    rw [actualControlledStateAfter_zero, Nat.add_zero]
  | succ i ih =>
    intro hi
    have hlt : i < actualControlledCount g a := by omega
    have hs := (actualControlledTraceFirstFinite g a ha).2 i hlt.le
    have hc := (actualControlledCountRecursion g (actualControlledStateAfter g a i) hs.1).2 (hs.2.2 hlt)
    rw [actualControlledStateAfter_succ]
    have hprev := ih hlt.le
    omega

theorem actualRetainedPrefixCountDecomposition : Targets.ActualRetainedPrefixCountDecomposition := by
  intro h k r hk hr e he hmin hbound hbudget
  dsimp only
  let g := prefixRemainderControl h (actualOrdinalNorm k)
  let C := actualControlledCount g r
  have hdiv := (actualMinExponentDivisibility k hk e).mp hmin
  have hsum := (actualDivisiblePrefixNormAddition k r hk hr e hdiv hbound).1
  have ht := actualPrefixControlTrace h k r hk hr e he hmin hbound hbudget
  dsimp only at ht
  have htotal := actualControlledTraceFirstFinite h (k + r) hsum
  have hle : C ≤ actualControlledCount h (k + r) := by
    by_contra hn
    have hlt : actualControlledCount h (k + r) < C := Nat.lt_of_not_ge hn
    have hnon := ht.2.2 _ hlt
    have homega : Ordinal.omega0 ≤ k + Ordinal.omega0 := le_add_self
    exact not_lt_of_ge (homega.trans hnon) htotal.1
  have hc := actualControlledCountTraceDecomposition h (k + r) hsum C hle
  rw [ht.1 C le_rfl] at hc
  change actualControlledCount h (k + r) =
    actualControlledCount h (k + actualControlledStateAfter g r C) + C at hc
  have hadd : actualControlledCount h (k + r) =
      C + actualControlledCount h (k + actualControlledStateAfter g r C) := by omega
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ht.2.1
  refine ⟨hle, hadd, n, hn, ?_⟩
  rw [hadd, hn]

private theorem segment_limitPart_tail (k : Ordinal) (hlim : Order.IsSuccLimit k) (n : Nat) :
    actualLimitPart (k + (n : Ordinal)) = k := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hlim.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualConstantBudgetFiniteTailCount : Targets.ActualConstantBudgetFiniteTailCount := by
  intro b n k hk hlim
  have hclosure := (actualFiniteTailClosureNorm k hk n).1
  have hn : Ordinal.omega0 ≤ k := Ordinal.omega0_le_of_isSuccLimit hlim
  have htailnon : Ordinal.omega0 ≤ k + (n : Ordinal) := hn.trans le_self_add
  have ht := (actualControlledCountRecursion (fun _ => b) (k + (n : Ordinal)) hclosure).2 htailnon
  have hkrec := (actualControlledCountRecursion (fun _ => b) k hk).2 hn
  have hstep : actualControlledStep (fun _ => b) (k + (n : Ordinal)) =
      actualControlledStep (fun _ => b) k := by
    change actualMaximumPredecessor (actualLimitPart (k + (n : Ordinal))) b =
      actualMaximumPredecessor (actualLimitPart k) b
    have hzero := segment_limitPart_tail k hlim 0
    simp only [Nat.cast_zero, add_zero] at hzero
    rw [segment_limitPart_tail k hlim n, hzero]
  rw [hstep] at ht
  exact ht.trans hkrec.symm

theorem actualConstantBudgetPrefixCountDecomposition : Targets.ActualConstantBudgetPrefixCountDecomposition := by
  intro b k r hk hr hlim e he hmin hbound hb
  have ht := actualRetainedPrefixCountDecomposition (fun _ => b) k r hk hr e he hmin hbound
    (fun _ => hb)
  dsimp only at ht
  obtain ⟨n, _, hc⟩ := ht.2.2
  have hg : prefixRemainderControl (fun _ => b) (actualOrdinalNorm k) =
      (fun _ => b - actualOrdinalNorm k) := rfl
  rw [hg, actualConstantBudgetFiniteTailCount b n k hk hlim] at hc
  exact hc

end LogicLineages.OrdinalComparison
