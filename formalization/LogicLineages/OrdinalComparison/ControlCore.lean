module
public import LogicLineages.OrdinalComparison.CoreControlTargets

@[expose] public section

/-!
# Elementary proofs for the exact numerical control

The general order hierarchy is unnecessary for these natural-number
proofs. This module expands increasingness into explicit inequalities.
It proves the same whole-domain numerical property as the source, not a
finite calculation or a conditional growth interface.
-/

namespace LogicLineages.OrdinalComparison

theorem core_iterate_self_le {f : Nat → Nat} (hf : ∀ x, x ≤ f x) (k x : Nat) :
    x ≤ f^[k] x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Nat.le_trans ih (hf _)

theorem core_iterate_time_le {f : Nat → Nat} (hf : ∀ x, x ≤ f x)
    (x : Nat) {k l : Nat} (hkl : k ≤ l) : f^[k] x ≤ f^[l] x := by
  induction hkl with
  | refl => exact Nat.le_refl _
  | @step l _ ih =>
      rw [Function.iterate_succ_apply']
      exact Nat.le_trans ih (hf _)

theorem core_iterate_increasing {f : Nat → Nat}
    (hf : ∀ {x y : Nat}, x < y → f x < f y) (k : Nat) :
    ∀ {x y : Nat}, x < y → f^[k] x < f^[k] y := by
  induction k with
  | zero => exact fun h => h
  | succ k ih =>
      intro x y hxy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hf (ih hxy)

theorem core_increasing_le {f : Nat → Nat}
    (hf : ∀ {x y : Nat}, x < y → f x < f y)
    {x y : Nat} (hxy : x ≤ y) : f x ≤ f y := by
  by_cases heq : x = y
  · rw [heq]
  · exact Nat.le_of_lt (hf (Nat.lt_of_le_of_ne hxy heq))

theorem core_self_lt_fastControl (j n : Nat) : n < fastControl j n := by
  induction j generalizing n with
  | zero => exact Nat.lt_two_pow_self
  | succ j ih =>
      change n < (fastControl j)^[n + 1] n
      rw [Function.iterate_succ_apply']
      exact Nat.lt_of_le_of_lt
        (core_iterate_self_le (fun x => Nat.le_of_lt (ih x)) n n) (ih _)

theorem core_fastControl_increasing (j : Nat) :
    ∀ {n m : Nat}, n < m → fastControl j n < fastControl j m := by
  induction j with
  | zero =>
      intro n m hnm
      exact Nat.pow_lt_pow_right (by decide) hnm
  | succ j ih =>
      intro n m hnm
      change (fastControl j)^[n + 1] n < (fastControl j)^[m + 1] m
      exact Nat.lt_of_lt_of_le (core_iterate_increasing ih (n + 1) hnm)
        (core_iterate_time_le (fun x => Nat.le_of_lt (core_self_lt_fastControl j x)) m
          (Nat.add_le_add_right (Nat.le_of_lt hnm) 1))

theorem core_fastControl_le_next (j n : Nat) :
    fastControl j n ≤ fastControl (j + 1) n := by
  change fastControl j n ≤ (fastControl j)^[n + 1] n
  have h := core_iterate_time_le
    (fun x => Nat.le_of_lt (core_self_lt_fastControl j x)) n
    (show 1 ≤ n + 1 from Nat.succ_le_succ (Nat.zero_le n))
  simpa only [Function.iterate_one, id_eq] using h

theorem core_fastControl_level_le (n : Nat) {i j : Nat} (hij : i ≤ j) :
    fastControl i n ≤ fastControl j n := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (core_fastControl_le_next j n)

theorem core_two_pow_le_fastControl (j n : Nat) : 2 ^ n ≤ fastControl j n :=
  core_fastControl_level_le n (Nat.zero_le j)

theorem core_two_tower_le_fastControl {j n : Nat} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    2 ^ (2 ^ n) ≤ fastControl j n := by
  have h := core_iterate_time_le
    (fun x => Nat.le_of_lt (core_self_lt_fastControl 0 x)) n
    (show 2 ≤ n + 1 from Nat.succ_le_succ hn)
  have hfirst : 2 ^ (2 ^ n) ≤ fastControl 1 n := by
    simpa [fastControl, Function.iterate_succ_apply'] using h
  exact Nat.le_trans hfirst (core_fastControl_level_le n hj)

theorem core_fastControl_step_growth (j n : Nat) :
    fastControl j (fastControl (j + 1) n + 1) ≤ fastControl (j + 1) (n + 1) := by
  have hi : (fastControl j)^[n + 1] n + 1 ≤ (fastControl j)^[n + 1] (n + 1) :=
    Nat.succ_le_of_lt
      (core_iterate_increasing (core_fastControl_increasing j) (n + 1) (Nat.lt_succ_self n))
  have h := core_increasing_le (core_fastControl_increasing j) hi
  simpa only [fastControl, Function.iterate_succ_apply'] using h

theorem core_Phi_increasing {n m : Nat} (hnm : n < m) : Phi n < Phi m :=
  core_fastControl_increasing 5 (Nat.add_lt_add_right hnm 100)

theorem core_self_lt_Phi (n : Nat) : n < Phi n := by
  exact Nat.lt_of_le_of_lt (Nat.le_add_right n 100)
    (core_self_lt_fastControl 5 (n + 100))

theorem core_two_pow_shift_le_Phi (n : Nat) : 2 ^ (n + 100) ≤ Phi n :=
  core_two_pow_le_fastControl 5 (n + 100)

theorem core_Phi_succ_gap (n : Nat) : 2 ^ (2 ^ (Phi n + 1)) ≤ Phi (n + 1) := by
  have hbase := core_two_tower_le_fastControl (j := 4) (n := Phi n + 1)
    (by decide) (Nat.succ_le_succ (Nat.zero_le _))
  have hstep := core_fastControl_step_growth 4 (n + 100)
  exact Nat.le_trans hbase
    (by simpa only [Phi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep)

theorem core_Phi_double_tower_gap (n : Nat) : 2 ^ (2 ^ Phi n) ≤ Phi (n + 1) := by
  have hinner : 2 ^ Phi n ≤ 2 ^ (Phi n + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hinner) (core_Phi_succ_gap n)

theorem coreNumericalGrowth : Targets.CoreNumericalGrowth :=
  ⟨fun _ _ h => core_Phi_increasing h, fun n =>
    ⟨core_self_lt_Phi n, core_two_pow_shift_le_Phi n, core_Phi_double_tower_gap n⟩⟩

#print axioms coreNumericalGrowth

end LogicLineages.OrdinalComparison
