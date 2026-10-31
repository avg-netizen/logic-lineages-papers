module
public import LogicLineages.OrdinalComparison.SourcePerturbedControlTargets
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace LogicLineages.OrdinalComparison.PerturbedControl.Proof

theorem ratio_limit (b : Nat) (H : Nat×Nat → Bool) : RatioLimit b H := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  refine ⟨N,?_⟩
  intro n hn
  have hpn : n<Phi n := self_lt_Phi n
  have hp : (0 : Real)<Phi n := by exact_mod_cast (show 0<Phi n by omega)
  have hNp : (N : Real)<Phi n := by exact_mod_cast (show N<Phi n by omega)
  have heN : (1 : Real)<ε*N := by
    have hh := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hep : (1 : Real)<ε*Phi n := by nlinarith
  have he : error b H n≤1 := by
    unfold error
    split_ifs <;> omega
  have he0 : (0 : Real)≤error b H n := by exact_mod_cast (Nat.zero_le (error b H n))
  have he1 : (error b H n : Real)≤1 := by exact_mod_cast he
  have hr : (control b H n : Real)/(Phi n : Real)-1=
      (error b H n : Real)/(Phi n : Real) := by
    rw [control,Nat.cast_add,add_div,div_self (ne_of_gt hp)]
    linarith
  rw [hr,abs_of_nonneg (div_nonneg he0 hp.le)]
  apply (div_lt_iff₀ hp).mpr
  nlinarith
end LogicLineages.OrdinalComparison.PerturbedControl.Proof
