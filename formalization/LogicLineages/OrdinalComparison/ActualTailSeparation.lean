module
public import LogicLineages.OrdinalComparison.ActualTailSeparationTargets
public import LogicLineages.OrdinalComparison.ActualTerminal

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualLimitPartMonotone : Targets.ActualLimitPartMonotone := by
  intro a b hab
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone
    ((Ordinal.mul_div_gc Ordinal.omega0_ne_zero).monotone_u hab)

theorem actualMaximumJointMonotone : Targets.ActualMaximumJointMonotone := by
  intro a a' ha haa heps b b' hbb
  have hm := actualMaximumPredecessor_correct a ha (haa.trans_lt heps) b
  have hm' := actualMaximumPredecessor_correct a' (ha.trans_le haa) heps b'
  exact hm'.2 ⟨hm.1.1.trans_le haa, hm.1.2.trans hbb⟩

theorem actualDescentJointMonotone : Targets.ActualDescentJointMonotone := by
  intro a a' hn haa heps hnorm
  have ha := haa.trans_lt heps
  have hn' := hn.trans haa
  have hd := actualNonfiniteDecomposition a hn ha
  have hd' := actualNonfiniteDecomposition a' hn' heps
  constructor
  · exact actualMaximumJointMonotone _ _ hd.2.1.bot_lt
      (actualLimitPartMonotone haa) hd'.1 _ _ (Phi_strictMono.monotone hnorm)
  · rw [actualDescentStepNorm a hn ha, actualDescentStepNorm a' hn' heps]
    exact Phi_strictMono.monotone hnorm

theorem actualReplacementCountJointMonotone : Targets.ActualReplacementCountJointMonotone := by
  intro a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro a' haa heps hnorm
      have ha := haa.trans_lt heps
      by_cases hf : a < Ordinal.omega0
      · have h := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).1 hf)
        change actualReplacementCount a = 0 at h
        rw [h]
        exact Nat.zero_le _
      · have hn := le_of_not_gt hf
        have hn' := hn.trans haa
        have hd := actualDescentStepStrict a hn ha
        have hd' := actualDescentStepStrict a' hn' heps
        have hj := actualDescentJointMonotone a a' hn haa heps hnorm
        have hi := ih (actualDescentStep a) hd (actualDescentStep a') hj.1
          (hd'.trans heps) hj.2
        have hc := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a ha).2 hn)
        have hc' := congrArg (fun p : Nat × Nat => p.2) ((actualTerminalRecursion a' heps).2 hn')
        change actualReplacementCount a = actualReplacementCount (actualDescentStep a) + 1 at hc
        change actualReplacementCount a' = actualReplacementCount (actualDescentStep a') + 1 at hc'
        rw [hc, hc']
        exact Nat.add_le_add_right hi 1

theorem controlIterateDoubleTowerGap : Targets.ControlIterateDoubleTowerGap := by
  intro L hL t
  cases L with
  | zero => omega
  | succ k =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hstrict := Phi_strictMono.iterate k (Nat.lt_succ_self t)
      have hinput : (Phi^[k]) t + 1 ≤ (Phi^[k]) (t + 1) := hstrict
      exact (Phi_double_tower_gap ((Phi^[k]) t)).trans (Phi_strictMono.monotone hinput)

private theorem tail_facts (a : Ordinal) (ha : a < epsilonZero) (n : Nat) :
    a + (n : Ordinal) < epsilonZero ∧
      actualOrdinalNorm (a + (n : Ordinal)) = actualOrdinalNorm a + n := by
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  have ht := (finiteTailCorrect r n).1
  rw [hr] at ht
  constructor
  · rw [← ht]
    exact normalRepresentationSound (finiteTail r n)
  · rw [← ht, actualOrdinalNorm_notationCorrespondence (finiteTail r n),
      (finiteTailCorrect r n).2, ← actualOrdinalNorm_notationCorrespondence r, hr]

theorem actualTailSeparation : Targets.ActualTailSeparation := by
  intro a ha hlim
  have gap : ∀ n : Nat, 2 ^ (actualCollapse (a + (n : Ordinal))) <
      actualCollapse (a + ((n + 1 : Nat) : Ordinal)) := by
    intro n
    let x := a + (n : Ordinal)
    let y := a + ((n + 1 : Nat) : Ordinal)
    let t := actualOrdinalNorm a + n
    have hx := tail_facts a ha n
    have hy := tail_facts a ha (n + 1)
    have hxy : x ≤ y := add_le_add_right (by exact_mod_cast Nat.le_succ n) a
    have hnorm : actualOrdinalNorm x ≤ actualOrdinalNorm y := by rw [hx.2, hy.2]; omega
    have hcount := actualReplacementCountJointMonotone x y hxy hy.1 hnorm
    have hdec := actualCompleteTerminalDecomposition a ha hlim t (Nat.le_add_right _ _)
    have hsub : t - actualOrdinalNorm a = n := Nat.add_sub_cancel_left _ _
    rw [hsub] at hdec
    have hpos : 1 ≤ actualReplacementCount x := hdec.2.2.1
    have hz : actualTerminalValue x = (Phi^[actualReplacementCount x]) t := hdec.2.1
    have hsmall : actualCollapse x < 2 * actualTerminalValue x := hdec.2.2.2.2
    have hnum : actualCollapse x < 2 ^ actualTerminalValue x :=
      hsmall.trans_le (Nat.mul_le_pow (by decide : 2 ≠ 1) _)
    have hexp : 2 ^ actualCollapse x < 2 ^ (2 ^ actualTerminalValue x) :=
      Nat.pow_lt_pow_right (by decide) hnum
    have hgap := controlIterateDoubleTowerGap (actualReplacementCount x) hpos t
    rw [← hz] at hgap
    have hiter := iterate_index_mono (fun z => (self_lt_Phi z).le) (t + 1) hcount
    have hyid := actualTerminalValueIdentities y hy.1
    have hny : actualOrdinalNorm y = t + 1 := by rw [hy.2]; dsimp [t]; omega
    have hzy : actualTerminalValue y = (Phi^[actualReplacementCount y]) (t + 1) := by
      simpa only [hny] using hyid.2
    have hlarge : 2 ^ (2 ^ actualTerminalValue x) ≤ actualTerminalValue y := by
      rw [hzy]
      exact hgap.trans hiter
    have hterminal : actualTerminalValue y ≤ actualCollapse y := by rw [hyid.1]; omega
    exact hexp.trans_le (hlarge.trans hterminal)
  refine ⟨gap, ?_⟩
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.lt_two_pow_self.trans (gap n)

end LogicLineages.OrdinalComparison
