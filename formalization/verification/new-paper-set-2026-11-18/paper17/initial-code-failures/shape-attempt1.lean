module
public import LogicLineages.PermittedControl.InitialCodeProgramsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem original_units_power_add (e r : Ordinal.{0}) (c : Nat) (hc : 0 < c)
    (hr : r < Ordinal.omega0^e) :
    originalGapUnits (Ordinal.omega0^e*(c : Ordinal)+r)=List.replicate c e++originalGapUnits r := by
  have hcnf := Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0
    (by exact_mod_cast hc.ne' : (c : Ordinal) ≠ 0) (Ordinal.natCast_lt_omega0 c) hr
  simp only [originalGapUnits,hcnf,List.flatMap_cons,Ordinal.card_nat,Cardinal.toNat_natCast]

 theorem original_units_omega (n : Nat) : originalGapUnits (Ordinal.omega0*(n : Ordinal))=List.replicate n (1 : Ordinal) := by
  cases n with
  | zero => simp [originalGapUnits]
  | succ n =>
    have h := original_units_power_add 1 0 (n+1) (by omega) (by simpa using Ordinal.omega0_pos)
    simpa [originalGapUnits] using h

 theorem original_units_quadratic_shape (E : Ordinal.{0}) (hE : (3 : Ordinal) ≤ E) (n : Nat) :
    originalGapUnits (Ordinal.omega0^E+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal))=
      E::(2 : Ordinal)::List.replicate n 1 := by
  have hr : Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^(2 : Ordinal) := by
    simpa using linear_below_square n 0
  have h2E : (2 : Ordinal) < E := (by norm_num : (2 : Ordinal) < 3).trans_le hE
  have htail : Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^E := by
    simpa only [mul_one] using Ordinal.opow_mul_add_lt_opow Ordinal.one_lt_omega0 hr h2E
  have h := original_units_power_add E (Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal)) 1 (by omega) htail
  have h' := original_units_power_add 2 (Ordinal.omega0*(n : Ordinal)) 1 (by omega) hr
  simpa only [Nat.cast_one,mul_one,←add_assoc,List.replicate_one,List.cons_append,List.nil_append,h',original_units_omega] using h

 theorem original_units_double_quadratic (n : Nat) :
    originalGapUnits (Ordinal.omega0^(2 : Ordinal)*2+Ordinal.omega0*(n : Ordinal))=
      (2 : Ordinal)::2::List.replicate n 1 := by
  have hr : Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^(2 : Ordinal) := by simpa using linear_below_square n 0
  have h := original_units_power_add 2 (Ordinal.omega0*(n : Ordinal)) 2 (by omega) hr
  simpa [original_units_omega] using h

 theorem original_quadratic_list_eval (delta E : Ordinal.{0}) (hd : delta < epsilonZero) (n : Nat)
    (hl : originalGapUnits delta=E::(2 : Ordinal)::List.replicate n 1) :
    delta=Ordinal.omega0^E+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) := by
  have h := original_units_eval delta hd
  rw [hl,List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,List.map_replicate,List.sum_replicate,
    Ordinal.opow_one,Ordinal.nsmul_eq_mul] at h
  exact h.symm.trans (add_assoc _ _ _).symm

end LogicLineages.PermittedControl
