module
public import LogicLineages.OrdinalComparison.ControlTargets
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Nat.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The literal Wilken--Weiermann numerical control

The base is exponentiation `2 ^ n`, not doubling. The recursive definition
retains the input-dependent number of iterations and the shift by 100.
No computation of a concrete large control value is needed by these proofs.
-/

namespace LogicLineages.OrdinalComparison

theorem iterate_self_le {f : Nat → Nat} (hf : ∀ x, x ≤ f x) (k x : Nat) :
    x ≤ f^[k] x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (hf _)

theorem iterate_index_mono {f : Nat → Nat} (hf : ∀ x, x ≤ f x) (x : Nat) :
    Monotone (fun k => f^[k] x) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [Function.iterate_succ_apply']
  exact hf _

theorem self_lt_fastControl (j n : Nat) : n < fastControl j n := by
  induction j generalizing n with
  | zero => exact Nat.lt_two_pow_self
  | succ j ih =>
      change n < (fastControl j)^[n + 1] n
      rw [Function.iterate_succ_apply']
      exact (iterate_self_le (fun x => (ih x).le) n n).trans_lt (ih _)

theorem fastControl_strictMono (j : Nat) : StrictMono (fastControl j) := by
  induction j with
  | zero =>
      intro n m h
      exact Nat.pow_lt_pow_right (by decide) h
  | succ j ih =>
      intro n m h
      change (fastControl j)^[n + 1] n < (fastControl j)^[m + 1] m
      apply ((ih.iterate (n + 1)) h).trans_le
      exact (iterate_index_mono (fun x => (self_lt_fastControl j x).le) m)
        (Nat.add_le_add_right h.le 1)

theorem fastControl_le_next (j n : Nat) :
    fastControl j n ≤ fastControl (j + 1) n := by
  change fastControl j n ≤ (fastControl j)^[n + 1] n
  have h := (iterate_index_mono (fun x => (self_lt_fastControl j x).le) n)
    (show 1 ≤ n + 1 by omega)
  simpa only [Function.iterate_one, id_eq] using h

theorem fastControl_level_mono (n : Nat) : Monotone (fun j => fastControl j n) :=
  monotone_nat_of_le_succ (fun j => fastControl_le_next j n)

theorem two_pow_le_fastControl (j n : Nat) : 2 ^ n ≤ fastControl j n :=
  (fastControl_level_mono n) (Nat.zero_le j)

theorem two_tower_le_fastControl {j n : Nat} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    2 ^ (2 ^ n) ≤ fastControl j n := by
  have h := (iterate_index_mono (fun x => (self_lt_fastControl 0 x).le) n)
    (show 2 ≤ n + 1 by omega)
  have hfirst : 2 ^ (2 ^ n) ≤ fastControl 1 n := by
    simpa [fastControl, Function.iterate_succ_apply'] using h
  exact hfirst.trans ((fastControl_level_mono n) hj)

/-- Increasing the seed also pays one additional whole iteration. -/
theorem fastControl_step_growth (j n : Nat) :
    fastControl j (fastControl (j + 1) n + 1) ≤ fastControl (j + 1) (n + 1) := by
  have hi : (fastControl j)^[n + 1] n + 1 ≤ (fastControl j)^[n + 1] (n + 1) :=
    Nat.succ_le_of_lt ((fastControl_strictMono j).iterate (n + 1) (Nat.lt_succ_self n))
  have h := (fastControl_strictMono j).monotone hi
  simpa only [fastControl, Function.iterate_succ_apply'] using h

theorem Phi_strictMono : StrictMono Phi := by
  intro n m h
  exact fastControl_strictMono 5 (by omega : n + 100 < m + 100)

theorem self_lt_Phi (n : Nat) : n < Phi n := by
  exact (show n < n + 100 by omega).trans (self_lt_fastControl 5 (n + 100))

theorem two_pow_shift_le_Phi (n : Nat) : 2 ^ (n + 100) ≤ Phi n :=
  two_pow_le_fastControl 5 (n + 100)

/-- A slightly stronger whole-domain version of the paper's displayed gap. -/
theorem Phi_succ_gap (n : Nat) : 2 ^ (2 ^ (Phi n + 1)) ≤ Phi (n + 1) := by
  have hbase := two_tower_le_fastControl (j := 4) (n := Phi n + 1)
    (by omega) (by omega)
  have hstep := fastControl_step_growth 4 (n + 100)
  exact hbase.trans (by simpa only [Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hstep)

theorem Phi_double_tower_gap (n : Nat) : 2 ^ (2 ^ Phi n) ≤ Phi (n + 1) := by
  have hinner : 2 ^ Phi n ≤ 2 ^ (Phi n + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact (Nat.pow_le_pow_right (by decide) hinner).trans (Phi_succ_gap n)

/-- The independently specified numerical target, with no correctness premise. -/
theorem numericalControlGrowth : Targets.NumericalControlGrowth :=
  ⟨Phi_strictMono, fun n =>
    ⟨self_lt_Phi n, two_pow_shift_le_Phi n, Phi_double_tower_gap n⟩⟩

#print axioms fastControl_strictMono
#print axioms Phi_succ_gap

end LogicLineages.OrdinalComparison
