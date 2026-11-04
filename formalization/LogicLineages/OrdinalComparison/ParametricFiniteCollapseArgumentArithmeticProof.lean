module
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Proof

private theorem naturalSum_zero (x : Ordinal.{0}) : ordinalNaturalSum x 0 = x := by
  simp only [ordinalNaturalSum, Ordinal.CNF.coeff_zero_right, add_zero,
    Ordinal.CNF.eval_coeff]

private theorem omega_cnf :
    Ordinal.CNF Ordinal.omega0 Ordinal.omega0 = [(1, 1)] := by
  simpa only [Ordinal.opow_one, mul_one, add_zero, Ordinal.CNF.zero_right] using
    Ordinal.CNF.opow_mul_add (e := 1) (x := 1) (y := 0)
      Ordinal.one_lt_omega0 one_ne_zero Ordinal.one_lt_omega0
      (by simpa only [Ordinal.opow_one] using Ordinal.omega0_pos)

theorem naturalProduct_omega_finite (a : Nat) :
    ordinalNaturalProduct Ordinal.omega0 (a : Ordinal) =
      Ordinal.omega0 * (a : Ordinal) := by
  by_cases ha : a = 0
  · subst a
    simp only [ordinalNaturalProduct, Nat.cast_zero, Ordinal.CNF.zero_right, omega_cnf,
      List.foldr_cons, List.foldr_nil, Ordinal.CNF.eval_zero_right, mul_zero]
  · have ha' : (a : Ordinal.{0}) ≠ 0 := by exact_mod_cast ha
    have hca := Ordinal.CNF.of_lt ha' (Ordinal.natCast_lt_omega0 a)
    simp only [ordinalNaturalProduct, omega_cnf, hca, List.foldr_cons,
      List.foldr_nil, add_zero, one_mul, naturalSum_zero, Ordinal.CNF.eval_single,
      Ordinal.opow_one]

theorem naturalSum_omega_finite (a b : Nat) :
    ordinalNaturalSum (Ordinal.omega0 * (a : Ordinal)) (b : Ordinal) =
      Ordinal.omega0 * (a : Ordinal) + (b : Ordinal) := by
  by_cases ha : a = 0
  · subst a
    simp only [Nat.cast_zero, mul_zero, ordinalNaturalSum, Ordinal.CNF.coeff_zero_right,
      zero_add, Ordinal.CNF.eval_coeff]
  · have ha' : (a : Ordinal.{0}) ≠ 0 := by exact_mod_cast ha
    have hhead : Ordinal.CNF.coeff Ordinal.omega0 (Ordinal.omega0 * (a : Ordinal)) =
        Finsupp.single 1 (a : Ordinal) := by
      simpa only [Ordinal.opow_one, add_zero, Ordinal.CNF.coeff_zero_right] using
        Ordinal.CNF.coeff_opow_mul_add (e := 1) (x := (a : Ordinal)) (y := 0)
          Ordinal.one_lt_omega0 ha' (Ordinal.natCast_lt_omega0 a)
          (by simpa only [Ordinal.opow_one] using Ordinal.omega0_pos)
    have hfull : Ordinal.CNF.coeff Ordinal.omega0
        (Ordinal.omega0 * (a : Ordinal) + (b : Ordinal)) =
        Finsupp.single 1 (a : Ordinal) + Ordinal.CNF.coeff Ordinal.omega0 (b : Ordinal) := by
      simpa only [Ordinal.opow_one] using
        Ordinal.CNF.coeff_opow_mul_add (e := 1) (x := (a : Ordinal)) (y := (b : Ordinal))
          Ordinal.one_lt_omega0 ha' (Ordinal.natCast_lt_omega0 a)
          (by simpa only [Ordinal.opow_one] using Ordinal.natCast_lt_omega0 b)
    unfold ordinalNaturalSum
    rw [hhead, ← hfull, Ordinal.CNF.eval_coeff]

theorem mixedArithmetic : Targets.MixedArithmetic :=
  ⟨naturalProduct_omega_finite, naturalSum_omega_finite⟩

end LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Proof
