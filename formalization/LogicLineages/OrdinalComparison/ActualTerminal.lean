module
public import LogicLineages.OrdinalComparison.ActualTerminalTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualTerminalRecursion : Targets.ActualTerminalRecursion := by
  intro a ha
  constructor
  · intro hf
    conv_lhs => rw [actualTerminalData, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_pos hf]
  · intro hn
    conv_lhs => rw [actualTerminalData, WellFounded.fix_eq]
    simp only [dif_pos ha, dif_neg (not_lt_of_ge hn)]
    rfl

private theorem terminal_nonfinite (a : Ordinal) (ha : a < epsilonZero)
    (hn : Ordinal.omega0 ≤ a) :
    actualTerminalValue a = actualTerminalValue (actualDescentStep a) ∧
      actualReplacementCount a = actualReplacementCount (actualDescentStep a) + 1 := by
  have h := (actualTerminalRecursion a ha).2 hn
  have hf := congrArg (fun p : Nat × Nat => p.1) h
  have hc := congrArg (fun p : Nat × Nat => p.2) h
  exact ⟨hf, hc⟩

private theorem terminal_finite (n : Nat) (ha : (n : Ordinal) < epsilonZero) :
    actualTerminalValue (n : Ordinal) = n ∧ actualReplacementCount (n : Ordinal) = 0 := by
  have h := (actualTerminalRecursion (n : Ordinal) ha).1 (Ordinal.natCast_lt_omega0 n)
  have h' : actualTerminalData (n : Ordinal) = (n, 0) := by
    simpa only [Ordinal.card_nat, Cardinal.toNat_natCast] using h
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

theorem actualTerminalFirstFinite : Targets.ActualTerminalFirstFinite := by
  intro a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro ha
      by_cases hf : a < Ordinal.omega0
      · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hf
        have ht := terminal_finite n ha
        rw [ht.1, ht.2]
        exact ⟨rfl, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
      · have hn := le_of_not_gt hf
        have hd := actualDescentStepStrict a hn ha
        have hi := ih (actualDescentStep a) hd (hd.trans ha)
        have ht := terminal_nonfinite a ha hn
        rw [ht.1, ht.2]
        constructor
        · rw [Function.iterate_succ_apply]
          exact hi.1
        · intro k hk
          cases k with
          | zero => exact hn
          | succ k =>
              rw [Function.iterate_succ_apply]
              exact hi.2 k (Nat.lt_of_succ_lt_succ hk)

theorem actualTerminalValueIdentities : Targets.ActualTerminalValueIdentities := by
  intro a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro ha
      by_cases hf : a < Ordinal.omega0
      · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hf
        have ht := terminal_finite n ha
        have hnorm : actualOrdinalNorm (n : Ordinal) = n := by
          have h := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
          rw [norm_ofNat] at h
          change actualOrdinalNorm (ONote.ofNat n).repr = n at h
          rwa [ONote.repr_ofNat] at h
        rw [ht.1, ht.2, actualCollapse_finiteValues, hnorm]
        exact ⟨(Nat.add_zero n).symm, rfl⟩
      · have hn := le_of_not_gt hf
        have hd := actualDescentStepStrict a hn ha
        have hi := ih (actualDescentStep a) hd (hd.trans ha)
        have ht := terminal_nonfinite a ha hn
        constructor
        · rw [actualDescentStepCollapse a hn ha, hi.1, ht.1, ht.2]
          omega
        · rw [ht.1, ht.2, Function.iterate_succ_apply]
          rw [hi.2, actualDescentStepNorm a hn ha]

private theorem actual_nonfinite_norm (a : Ordinal) (ha : a < epsilonZero)
    (hn : Ordinal.omega0 ≤ a) : 2 ≤ actualOrdinalNorm a := by
  obtain ⟨⟨r, hr⟩, heq⟩ := normalRepresentationComplete a ha
  rw [← heq, actualOrdinalNorm_notationCorrespondence ⟨r, hr⟩]
  have hnr : Ordinal.omega0 ≤ r.repr := by rwa [heq]
  cases r with
  | zero => exact False.elim (not_le_of_gt Ordinal.omega0_pos hnr)
  | oadd e c t =>
      have he : e ≠ 0 := by
        intro he
        have ht : t = 0 := hr.zero_of_zero he
        have hf : (ONote.oadd e c t).repr < Ordinal.omega0 := by
          simpa [ONote.repr, he, ht] using Ordinal.natCast_lt_omega0 (c : Nat)
        exact not_le_of_gt hf hnr
      have hw : 0 < Vendor.R1.treeWeight e :=
        Nat.pos_of_ne_zero (fun h => he ((treeWeight_eq_zero_iff e).mp h))
      have hm := Nat.le_mul_of_pos_left (1 + Vendor.R1.treeWeight e) c.pos
      simp only [Vendor.R1.treeWeight]
      omega

private theorem control_iteration_increases (t k : Nat) : t + k ≤ (Phi^[k]) t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := self_lt_Phi ((Phi^[k]) t)
      omega

private theorem terminal_initial (a : Ordinal) (ha : a < epsilonZero) (n : Nat) :
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

theorem actualCompleteTerminalDecomposition : Targets.ActualCompleteTerminalDecomposition := by
  intro a ha hlim t ht
  let initial := a + ((t - actualOrdinalNorm a : Nat) : Ordinal)
  have hi := terminal_initial a ha (t - actualOrdinalNorm a)
  have hnorm : actualOrdinalNorm initial = t := by
    rw [hi.2, Nat.add_sub_of_le ht]
  have hnon : Ordinal.omega0 ≤ initial :=
    (Ordinal.omega0_le_of_isSuccLimit hlim).trans le_self_add
  have hv := actualTerminalValueIdentities initial hi.1
  have hpos : 0 < actualReplacementCount initial := by
    rw [(terminal_nonfinite initial hi.1 hnon).2]
    exact Nat.zero_lt_succ _
  have hz : actualTerminalValue initial = (Phi^[actualReplacementCount initial]) t := by
    simpa only [hnorm] using hv.2
  have ht2 : 2 ≤ t := (actual_nonfinite_norm a ha (Ordinal.omega0_le_of_isSuccLimit hlim)).trans ht
  have hbound := control_iteration_increases t (actualReplacementCount initial)
  rw [← hz] at hbound
  refine ⟨hv.1, hz, hpos, ?_, ?_⟩
  · change actualTerminalValue initial < actualCollapse initial
    rw [hv.1]
    omega
  · change actualCollapse initial < 2 * actualTerminalValue initial
    rw [hv.1]
    omega

end LogicLineages.OrdinalComparison
