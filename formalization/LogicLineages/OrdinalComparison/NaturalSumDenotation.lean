module
public import LogicLineages.OrdinalComparison.NaturalSumDenotationTargets
public import LogicLineages.OrdinalComparison.NaturalSum

@[expose] public section

/-! Bridge the executable hereditary-notation merge to Mathlib's genuine
ordinal Cantor coefficients. Classical equality is used only for an auxiliary
semantic coefficient function, not for the natural-sum algorithm. -/

namespace LogicLineages.OrdinalComparison

noncomputable def coefficientAtOrdinal : ONote → Ordinal → Nat
  | .zero, _ => 0
  | .oadd e c t, q => by
      classical
      exact (if e.repr = q then (c : Nat) else 0) + coefficientAtOrdinal t q

theorem actual_coefficient_eq_cast (a : ONote) (ha : ONote.NF a) (q : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 a.repr q = (coefficientAtOrdinal a q : Ordinal) := by
  classical
  induction a with
  | zero => simp only [ONote.repr_zero, Ordinal.CNF.coeff_zero_apply, coefficientAtOrdinal,
      Nat.cast_zero]
  | oadd e c t ihe iht =>
      have hc : (c : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
      rw [ONote.repr, Ordinal.CNF.coeff_opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt]
      by_cases he : e.repr = q
      · simp only [Finsupp.add_apply, Finsupp.single_apply, coefficientAtOrdinal,
          he, ↓reduceIte, iht ha.snd, Nat.cast_add]
      · simp only [Finsupp.add_apply, Finsupp.single_apply, coefficientAtOrdinal,
          he, ↓reduceIte, iht ha.snd, Nat.cast_add, Nat.cast_zero, zero_add]

theorem rawNaturalSum_actual_coefficients : ∀ (a b : ONote) (q : Ordinal),
    coefficientAtOrdinal (rawNaturalSum a b) q =
      coefficientAtOrdinal a q + coefficientAtOrdinal b q
  | .zero, b, q => by simp only [rawNaturalSum, coefficientAtOrdinal, Nat.zero_add]
  | a, .zero, q => by simp only [rawNaturalSum, coefficientAtOrdinal, Nat.add_zero]
  | a@(.oadd e c t), b@(.oadd f d u), q => by
      classical
      cases h : ONote.cmp e f with
      | lt =>
          simp only [rawNaturalSum, h, coefficientAtOrdinal,
            rawNaturalSum_actual_coefficients a u q]
          omega
      | eq =>
          have hef : e = f := ONote.eq_of_cmp_eq h
          subst f
          simp only [rawNaturalSum, h, coefficientAtOrdinal,
            rawNaturalSum_actual_coefficients t u q, PNat.add_coe]
          split <;> omega
      | gt =>
          simp only [rawNaturalSum, h, coefficientAtOrdinal,
            rawNaturalSum_actual_coefficients t b q]
          omega
termination_by a b _ => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem naturalSumOrdinalCoefficients : Targets.NaturalSumOrdinalCoefficients naturalSum := by
  intro a b q
  rw [actual_coefficient_eq_cast (naturalSum a b).1 (naturalSum a b).2 q,
    actual_coefficient_eq_cast a.1 a.2 q, actual_coefficient_eq_cast b.1 b.2 q]
  simpa only [naturalSum, rawNaturalSum_actual_coefficients, Nat.cast_add]

end LogicLineages.OrdinalComparison
