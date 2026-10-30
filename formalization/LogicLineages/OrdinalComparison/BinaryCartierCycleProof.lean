module
public import LogicLineages.OrdinalComparison.BinaryCartierCycleTargets
public import LogicLineages.OrdinalComparison.BinaryCartierUpdateProof
public import Mathlib.Data.Fintype.Pigeonhole
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualBinaryProperNumeratorFinite : Targets.ActualBinaryProperNumeratorFinite := by
  intro d
  let v : ActualBinaryProperNumerator d → (Fin (actualBinarySourceDimension d) → ZMod 2) :=
    fun U i => U.val.coeff i.val
  apply Finite.of_injective v
  intro U V h
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  by_cases hn : n < actualBinarySourceDimension d
  · exact congrFun h ⟨n, hn⟩
  · have hle : (actualBinarySourceDimension d : WithBot Nat) ≤ (n : WithBot Nat) :=
      Nat.cast_le.mpr (Nat.le_of_not_gt hn)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (U.property.trans_le hle),
      Polynomial.coeff_eq_zero_of_degree_lt (V.property.trans_le hle)]

theorem actualBinaryCartierNumeratorIteration : Targets.ActualBinaryCartierNumeratorIteration := by
  intro d U j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, actualBinaryRationalCartierUpdate,
      Function.iterate_succ_apply']
    rfl

theorem actualBinaryCartierEventualCycle : Targets.ActualBinaryCartierEventualCycle := by
  intro d U
  letI := actualBinaryProperNumeratorFinite d
  let f := actualBinaryProperNumeratorStep d
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun j : Nat => f^[j] U)
  have hcollision : ∃ j p : Nat, 0 < p ∧ f^[j + p] U = f^[j] U := by
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · refine ⟨m, n - m, by omega, ?_⟩
      simpa only [Nat.add_sub_of_le hlt.le] using heq.symm
    · refine ⟨n, m - n, by omega, ?_⟩
      simpa only [Nat.add_sub_of_le hlt.le] using heq
  obtain ⟨j, p, hp, heq⟩ := hcollision
  refine ⟨j, p, hp, ?_⟩
  intro k
  rw [actualBinaryCartierNumeratorIteration, actualBinaryCartierNumeratorIteration]
  have h := congrArg (fun V => f^[k] V) heq
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h
  have hi : f^[j + k + p] U = f^[j + k] U := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  exact congrArg (fun V : ActualBinaryProperNumerator d =>
    actualBinaryRationalDifferential d V.val) hi

end LogicLineages.OrdinalComparison
