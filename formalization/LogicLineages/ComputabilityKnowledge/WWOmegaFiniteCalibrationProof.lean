module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWOmegaFiniteCalibration
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section

/-! Actual natural-ordinal arithmetic calibration for the source padding,
authored after exact target freeze; includes all zero numeric edgecases. -/
namespace LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof

open LogicLineages.OrdinalComparison
open WWOmegaFiniteCalibration

private theorem omega_cnf : Ordinal.CNF Ordinal.omega0 Ordinal.omega0 = [(1, 1)] := by
  simpa only [Ordinal.opow_one, mul_one, add_zero, Ordinal.CNF.zero_right] using
    Ordinal.CNF.opow_mul_add (e := 1) (x := 1) (y := 0) Ordinal.one_lt_omega0
      one_ne_zero Ordinal.one_lt_omega0 (by simp)

private theorem finite_coeff (n : Nat) :
    Ordinal.CNF.coeff Ordinal.omega0 (n : Ordinal.{0}) = Finsupp.single 0 (n : Ordinal) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Ordinal.CNF.coeff_zero_right, Finsupp.single_zero]
  · have hne : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn
    simpa only [Ordinal.opow_zero, one_mul, add_zero, Ordinal.CNF.coeff_zero_right] using
      Ordinal.CNF.coeff_opow_mul_add (e := 0) (y := 0) Ordinal.one_lt_omega0 hne
        (Ordinal.natCast_lt_omega0 n) (by simp)

private theorem omega_coeff (n : Nat) :
    Ordinal.CNF.coeff Ordinal.omega0 (Ordinal.omega0 * (n : Ordinal.{0})) = Finsupp.single 1 (n : Ordinal) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, mul_zero, Ordinal.CNF.coeff_zero_right, Finsupp.single_zero]
  · have hne : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn
    simpa only [Ordinal.opow_one, add_zero, Ordinal.CNF.coeff_zero_right] using
      Ordinal.CNF.coeff_opow_mul_add (e := 1) (y := 0) Ordinal.one_lt_omega0 hne
        (Ordinal.natCast_lt_omega0 n) (by simp)

theorem productCalibration : Comparators.WWOmegaFiniteCalibration.ProductCalibration := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [ordinalNaturalProduct, Ordinal.CNF.zero_right, Ordinal.CNF.eval_zero_right]
  · have hne : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn
    have hcnf := Ordinal.CNF.of_lt hne (Ordinal.natCast_lt_omega0 n)
    have hone : ordinalNaturalSum 1 0 = 1 := by
      simpa only [Nat.cast_one, Nat.cast_zero, Nat.add_zero] using
        WWOrdinalTermSemanticsProof.naturalSum_finite 1 0
    simp only [ordinalNaturalProduct, omega_cnf, hcnf, List.foldr_cons, List.foldr_nil,
      hone, one_mul, add_zero, Ordinal.CNF.eval_single, Ordinal.opow_one]

theorem sumCalibration : Comparators.WWOmegaFiniteCalibration.SumCalibration := by
  intro n g
  unfold ordinalNaturalSum
  rw [omega_coeff, finite_coeff, Ordinal.CNF.eval_single_add']
  · simp only [Ordinal.opow_one, Ordinal.CNF.eval_single, Ordinal.opow_zero, one_mul]
  · intro e he
    have he0 : e = 0 := by
      by_contra hne
      have hz : (Finsupp.single 0 (g : Ordinal.{0}) : Ordinal →₀ Ordinal) e = 0 :=
        Finsupp.single_eq_of_ne hne
      exact (Finsupp.mem_support_iff.mp he) hz
    subst e
    exact zero_lt_one

private theorem omega_finite_below (n g : Nat) :
    Ordinal.omega0 * (n : Ordinal.{0}) + (g : Ordinal.{0}) < epsilonZero := by
  have hone : (1 : Ordinal.{0}) < epsilonZero := by
    simpa only [Nat.cast_one] using (WWOrdinalTermSemanticsProof.finiteNorm 1).1
  have hw : Ordinal.omega0 < epsilonZero := by
    have hp : Ordinal.omega0 ^ (1 : Ordinal.{0}) < epsilonZero :=
      (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr hone
    simpa only [Ordinal.opow_one] using hp
  exact epsilonZero_add_principal (epsilonZero_add_principal.mul_natCast_lt hw n)
    (WWOrdinalTermSemanticsProof.finiteNorm g).1

theorem normCalibration : Comparators.WWOmegaFiniteCalibration.NormCalibration := by
  intro n g
  rw [block, productCalibration, sumCalibration]
  exact ⟨omega_finite_below n g, actualFiniteHeadNorm n g⟩

theorem collapseCalibration : Comparators.WWOmegaFiniteCalibration.CollapseCalibration := by
  intro n g
  have h := actualCollapseDominatesNorm (block n g) (normCalibration n g).1
  rw [(normCalibration n g).2] at h
  exact ⟨h, by omega⟩

theorem wwOmegaFiniteCalibration : Comparators.WWOmegaFiniteCalibration.Target :=
  ⟨productCalibration, sumCalibration, normCalibration, collapseCalibration⟩

end LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof
