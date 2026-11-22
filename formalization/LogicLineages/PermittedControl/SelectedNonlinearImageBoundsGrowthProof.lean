module
public import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsTargets
import LogicLineages.PermittedControl.FactorialProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.OrdinalComparison.Control
import Mathlib.Data.Nat.Log

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedNonlinearImageBounds
open OrdinalComparison

theorem orbitGrowth (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (x i : Nat) : x + i ≤ f^[i] x := by
  have admissible := (selected_threshold_admissible f B selected).2
  induction i with
  | zero => simp
  | succ i ih =>
    have size := G_large (f^[i] x)
    have control := admissible (f^[i] x)
    rw [Function.iterate_succ_apply']
    omega

private theorem selectedAdjacent (f : Nat → Nat) (B : Nat)
    (selected : SelectedWithThreshold f B) (n : Nat) : 2 ^ (2 ^ f n) ≤ f (n + 1) := by
  rcases selected with ⟨rfl,_⟩ | ⟨b,rfl,_⟩
  · exact factorialControl_separation n
  · exact nearControl_separation b n

theorem distinctFullValueSeparation : DistinctFullValueSeparation := by
  intro f B selected p q ordered
  have strict := (selected_threshold_admissible f B selected).1
  have next : p + 1 ≤ q := Nat.succ_le_of_lt (strict.lt_iff_lt.mp ordered)
  have separation := (selectedAdjacent f B selected p).trans (strict.monotone next)
  have power : 2 ^ f p ≤ f q :=
    (Nat.pow_le_pow_right (by decide) (Nat.lt_two_pow_self (n := f p)).le).trans separation
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by decide) power

theorem rawCoordinateLogBound : RawCoordinateLogBound := by
  intro f B selected z C bound
  have base : 2 ^ z ≤ G z :=
    (Nat.pow_le_pow_right (by decide) (show z ≤ z + 100 by omega)).trans
      (two_pow_shift_le_Phi z)
  have power := base.trans (((selected_threshold_admissible f B selected).2 z).trans bound)
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by decide) power

end LogicLineages.PermittedControl.SelectedNonlinearImageBounds
