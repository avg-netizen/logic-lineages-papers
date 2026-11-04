module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseTargets
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Proof

theorem pair_facts (p : Nat × Nat) :
    ordinal p < epsilonZero ∧ actualOrdinalNorm (ordinal p) = pairNorm p := by
  refine ⟨?_, actualFiniteHeadNorm p.1 p.2⟩
  rcases p with ⟨a, b⟩
  cases a with
  | zero =>
      have hs := normalRepresentationSound (NONote.ofNat b)
      change (ONote.ofNat b).repr < epsilonZero at hs
      simpa only [ordinal, Nat.cast_zero, mul_zero, zero_add, ONote.repr_ofNat] using hs
  | succ a =>
      have ht : ONote.NFBelow (ONote.ofNat b) (ONote.ofNat 1).repr := by
        apply ONote.NF.below_of_lt' _ (ONote.nf_ofNat b)
        simp only [ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one]
        exact Ordinal.natCast_lt_omega0 b
      let r : NONote := ⟨ONote.oadd (ONote.ofNat 1) ⟨a + 1, Nat.succ_pos a⟩ (ONote.ofNat b),
        ONote.NF.oadd (ONote.nf_ofNat 1) _ ht⟩
      have hr : r.1.repr = ordinal (a + 1, b) := by
        change Ordinal.omega0 ^ (ONote.ofNat 1).repr * ((a + 1 : Nat) : Ordinal) +
          (ONote.ofNat b).repr = _
        simp only [ordinal, ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one]
      rw [← hr]
      exact normalRepresentationSound r

theorem pair_lt_next_head (p : Nat × Nat) :
    ordinal p < Ordinal.omega0 * ((p.1 + 1 : Nat) : Ordinal) := by
  simpa only [ordinal, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
    (add_lt_add_right (Ordinal.natCast_lt_omega0 p.2)
      (Ordinal.omega0 * (p.1 : Ordinal)))

theorem pair_lt {q p : Nat × Nat} (h : Below q p) : ordinal q < ordinal p := by
  rcases h with h | ⟨ha, hb⟩
  · apply (pair_lt_next_head q).trans_le
    apply le_trans _ le_self_add
    apply mul_le_mul_left'
    exact_mod_cast Nat.succ_le_of_lt h
  · unfold ordinal
    rw [ha]
    apply add_lt_add_right
    exact_mod_cast hb

theorem pair_injective : Function.Injective ordinal := by
  intro p q h
  have ha : p.1 = q.1 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh := pair_lt (p := q) (q := p) (Or.inl hlt)
      rw [h] at hh
      exact (lt_irrefl _ hh)
    · have hh := pair_lt (p := p) (q := q) (Or.inl hgt)
      rw [h] at hh
      exact (lt_irrefl _ hh)
  have hb : p.2 = q.2 := by
    unfold ordinal at h
    rw [ha] at h
    have hh := add_left_cancel h
    exact_mod_cast hh
  exact Prod.ext ha hb

theorem pair_predecessor (p : Nat × Nat) (x : Ordinal.{0}) :
    x < ordinal p ↔ ∃ q : Nat × Nat, Below q p ∧ x = ordinal q := by
  constructor
  · intro hx
    obtain ⟨q, hq, r, hr, heq⟩ :=
      Ordinal.lt_mul_iff.mp (hx.trans (pair_lt_next_head p))
    obtain ⟨a, ha⟩ := Ordinal.eq_natCast_of_le_natCast hq.le
    obtain ⟨b, hb⟩ := Ordinal.lt_omega0.mp hr
    rw [ha, hb] at heq
    have hap : a ≤ p.1 := by
      rw [ha] at hq
      have : a < p.1 + 1 := by exact_mod_cast hq
      omega
    refine ⟨(a, b), ?_, heq⟩
    rcases lt_or_eq_of_le hap with hlt | he
    · exact Or.inl hlt
    · refine Or.inr ⟨he, ?_⟩
      rw [heq] at hx
      unfold ordinal at hx
      rw [he] at hx
      have hh : (b : Ordinal) < (p.2 : Ordinal) := (add_lt_add_iff_left _).mp hx
      exact_mod_cast hh
  · rintro ⟨q, hq, rfl⟩
    exact pair_lt hq

theorem exactRepresentation : Targets.ExactRepresentation :=
  ⟨pair_facts, pair_injective, pair_predecessor⟩

end LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse.Proof
