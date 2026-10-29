module
public import LogicLineages.OrdinalComparison.ActualFiniteHeadTargets
public import LogicLineages.OrdinalComparison.ActualSinglePredecessor

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem finite_head_facts (k n : Nat) :
    Ordinal.omega0 * (k : Ordinal) + (n : Ordinal) < epsilonZero ∧
      actualOrdinalNorm (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = 2 * k + n := by
  cases k with
  | zero =>
      have hs := normalRepresentationSound (NONote.ofNat n)
      have hn := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
      rw [norm_ofNat] at hn
      change (ONote.ofNat n).repr < epsilonZero at hs
      change actualOrdinalNorm (ONote.ofNat n).repr = n at hn
      rw [ONote.repr_ofNat] at hs hn
      simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero] using And.intro hs hn
  | succ k =>
      have ht : ONote.NFBelow (ONote.ofNat n) (ONote.ofNat 1).repr := by
        apply ONote.NF.below_of_lt' _ (ONote.nf_ofNat n)
        simp only [ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one]
        exact Ordinal.natCast_lt_omega0 n
      let r : NONote := ⟨ONote.oadd (ONote.ofNat 1) ⟨k + 1, Nat.succ_pos k⟩ (ONote.ofNat n),
        ONote.NF.oadd (ONote.nf_ofNat 1) _ ht⟩
      have hr : r.1.repr = Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) + (n : Ordinal) := by
        change Ordinal.omega0 ^ (ONote.ofNat 1).repr * ((k + 1 : Nat) : Ordinal) +
          (ONote.ofNat n).repr = _
        simp only [ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one]
      constructor
      · rw [← hr]
        exact normalRepresentationSound r
      · rw [← hr, actualOrdinalNorm_notationCorrespondence r]
        have hn : Vendor.R1.treeWeight (ONote.ofNat n) = n := norm_ofNat n
        have h1 : Vendor.R1.treeWeight (ONote.ofNat 1) = 1 := norm_ofNat 1
        change (k + 1) * (1 + Vendor.R1.treeWeight (ONote.ofNat 1)) +
          Vendor.R1.treeWeight (ONote.ofNat n) = _
        rw [hn, h1]
        omega

theorem actualFiniteHeadNorm : Targets.ActualFiniteHeadNorm :=
  fun k n => (finite_head_facts k n).2

private theorem finite_head_lt (k n : Nat) :
    Ordinal.omega0 * (k : Ordinal) + (n : Ordinal) <
      Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) := by
  simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
    (add_lt_add_right (Ordinal.natCast_lt_omega0 n) (Ordinal.omega0 * (k : Ordinal)))

theorem actualFiniteHeadMaximum : Targets.ActualFiniteHeadMaximum := by
  intro k b hb
  have hk : 2 * k ≤ b := by omega
  have hpos : 0 < Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) :=
    mul_pos Ordinal.omega0_pos (by exact_mod_cast Nat.succ_pos k)
  have heps : Ordinal.omega0 * ((k + 1 : Nat) : Ordinal) < epsilonZero := by
    simpa only [Nat.cast_zero, add_zero] using (finite_head_facts (k + 1) 0).1
  symm
  apply actualMaximumPredecessor_unique _ hpos heps b
  constructor
  · refine ⟨finite_head_lt k (b - 2 * k), ?_⟩
    rw [actualFiniteHeadNorm, Nat.add_sub_of_le hk]
  · intro x hx
    obtain ⟨q, hq, r, hr, heq⟩ := Ordinal.lt_mul_iff.mp hx.1
    obtain ⟨j, hj⟩ := Ordinal.eq_natCast_of_le_natCast hq.le
    obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hr
    rw [hj, hm] at heq
    have hjk : j ≤ k := by
      rw [hj] at hq
      have : j < k + 1 := by exact_mod_cast hq
      omega
    rw [heq]
    rcases lt_or_eq_of_le hjk with hlt | rfl
    · apply (finite_head_lt j m).le.trans
      apply le_trans _ le_self_add
      apply mul_le_mul_left'
      exact_mod_cast Nat.succ_le_of_lt hlt
    · have hnorm : 2 * j + m ≤ b := by
        have h := hx.2
        rw [heq, actualFiniteHeadNorm j m] at h
        exact h
      apply add_le_add_right
      exact_mod_cast (show m ≤ b - 2 * j by omega)

theorem actualFiniteHeadCollapse : Targets.ActualFiniteHeadCollapse := by
  intro k
  induction k with
  | zero =>
      intro n
      simp only [Nat.cast_zero, mul_zero, zero_add,
        Function.iterate_zero_apply, Nat.mul_zero, Nat.add_zero]
      exact actualCollapse_finiteValues n
  | succ k ih =>
      intro n
      let a : Ordinal := Ordinal.omega0 * ((k + 1 : Nat) : Ordinal)
      have ha : a < epsilonZero := by
        simpa only [Nat.cast_zero, add_zero] using (finite_head_facts (k + 1) 0).1
      have hlim : Order.IsSuccLimit a :=
        Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
          (by exact_mod_cast Nat.succ_pos k)
      have hn : actualOrdinalNorm a = 2 * (k + 1) := by
        simpa only [Nat.cast_zero, add_zero, Nat.add_zero] using actualFiniteHeadNorm (k + 1) 0
      let b := Phi (2 * (k + 1) + n)
      have hb : 2 * (k + 1) ≤ b := by
        have h := self_lt_Phi (2 * (k + 1) + n)
        omega
      have hrec := actualSinglePredecessorRecurrence a ha hlim n
      rw [hn, actualFiniteHeadMaximum k b hb, ih] at hrec
      have hk : 2 * k ≤ b := by omega
      rw [Nat.add_sub_of_le hk] at hrec
      rw [hrec, Function.iterate_succ_apply]
      rfl

end LogicLineages.OrdinalComparison
