module
public import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section

/-! Complete hereditary Cantor representation below the calibrated epsilon
zero. Transfinite induction applies to both the leading exponent and the
remainder. The leading exponent is strictly smaller because equality would
already make the input a fixed point of actual omega power.
-/

namespace LogicLineages.OrdinalComparison

theorem omega_log_lt_below_epsilonZero (b : Ordinal) (hb : b < epsilonZero)
    (hzero : b ≠ 0) : Ordinal.log Ordinal.omega0 b < b := by
  rcases lt_or_eq_of_le (Ordinal.log_le_self Ordinal.omega0 b) with hlt | heq
  · exact hlt
  · have hpow : Ordinal.omega0 ^ b ≤ b := by
      simpa only [heq] using Ordinal.opow_log_le_self Ordinal.omega0 hzero
    have hfixed : Ordinal.omega0 ^ b = b :=
      le_antisymm hpow (Ordinal.right_le_opow b Ordinal.one_lt_omega0)
    exact False.elim ((not_le_of_gt hb) (epsilonZeroCalibration.2 b hfixed))

theorem normalRepresentationComplete : Targets.NormalRepresentationComplete := by
  intro b
  induction b using Ordinal.lt_wf.induction with
  | h b ih =>
      intro hb
      by_cases hzero : b = 0
      · subst b
        exact ⟨0, rfl⟩
      · have hlog := omega_log_lt_below_epsilonZero b hb hzero
        have hrem : b % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 b) < b :=
          Ordinal.mod_opow_log_lt_self Ordinal.omega0 hzero
        obtain ⟨e, he⟩ := ih (Ordinal.log Ordinal.omega0 b) hlog (hlog.trans hb)
        obtain ⟨t, ht⟩ := ih
          (b % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 b)) hrem (hrem.trans hb)
        obtain ⟨c, hc⟩ := Ordinal.lt_omega0.mp
          (Ordinal.div_opow_log_lt b Ordinal.one_lt_omega0)
        have hcpos : 0 < c := by
          have hpos := Ordinal.div_opow_log_pos Ordinal.omega0 hzero
          rw [hc] at hpos
          exact_mod_cast hpos
        have htail : ONote.NFBelow t.1 e.1.repr := by
          refine ONote.NF.below_of_lt' ?_ t.2
          rw [ht, he]
          exact Ordinal.mod_lt b
            (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
        let result : NONote :=
          ⟨ONote.oadd e.1 ⟨c, hcpos⟩ t.1, ONote.NF.oadd e.2 _ htail⟩
        refine ⟨result, ?_⟩
        change Ordinal.omega0 ^ e.1.repr * (c : Ordinal) + t.1.repr = b
        rw [he, ht, ← hc]
        exact Ordinal.div_add_mod b
          (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 b)

end LogicLineages.OrdinalComparison
