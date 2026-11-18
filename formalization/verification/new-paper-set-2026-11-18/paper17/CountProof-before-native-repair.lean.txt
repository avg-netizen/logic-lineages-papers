module
public import LogicLineages.PermittedControl.FunnelProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

theorem count_initial_facts (lam : Ordinal) (t : Nat) (ha : lam < epsilonZero)
    (hl : Order.IsSuccLimit lam) (ht : actualOrdinalNorm lam ≤ t) :
    countInitial lam t < epsilonZero ∧ actualOrdinalNorm (countInitial lam t) = t ∧
    Ordinal.omega0 ≤ countInitial lam t := by
  have h := actualFiniteTailClosureNorm lam ha (t - actualOrdinalNorm lam)
  refine ⟨h.1, ?_, (Ordinal.omega0_le_of_isSuccLimit hl).trans le_self_add⟩
  change actualOrdinalNorm (lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)) = t
  rw [h.2, Nat.add_sub_of_le ht]

theorem count_endpoint_facts (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam : Ordinal) (t : Nat) (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam)
    (ht : actualOrdinalNorm lam ≤ t) :
    completeEndpoint f lam t = f^[completeCount f lam t] t ∧
    headCollapse f lam t = completeEndpoint f lam t + completeCount f lam t ∧
    0 < completeCount f lam t ∧ 2 ∣ completeEndpoint f lam t := by
  have had := selected_threshold_admissible f B hf
  have hi := count_initial_facts lam t ha hl ht
  have hs := terminalSemantics f had.1 had.2 (countInitial lam t) hi.1
  have hz : completeEndpoint f lam t = f^[completeCount f lam t] t := by
    simpa only [completeEndpoint, completeCount, hi.2.1] using hs.2.2.2.1
  have hp : 0 < completeCount f lam t := (hs.2.2.2.2 hi.2.2).1
  refine ⟨hz, hs.2.2.1, hp, ?_⟩
  rw [hz]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : completeCount f lam t ≠ 0)
  rw [hk, Function.iterate_succ_apply']
  exact selected_even f B hf _

theorem endpoint_potential (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m : Nat) (lam : Ordinal) (t : Nat) (hm : 0 < m) (ha : lam < epsilonZero)
    (hl : Order.IsSuccLimit lam) (ht : max (actualOrdinalNorm lam) (max m B) ≤ t) :
    Int.ModEq (m : Int) (potential (completeEndpoint f lam t) : Int)
      ((potential t : Int) - (completeCount f lam t : Int)) := by
  have hs := count_endpoint_facts f B hf lam t ha hl (by omega)
  rw [hs.1]
  exact selected_orbit f B hf m t _ hm (by omega)

theorem endpoint_even_cast (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam : Ordinal) (t : Nat) (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam)
    (ht : actualOrdinalNorm lam ≤ t) :
    (completeEndpoint f lam t : Int) = 2 * (potential (completeEndpoint f lam t) : Int) := by
  have hd := Nat.mod_eq_zero_of_dvd (count_endpoint_facts f B hf lam t ha hl ht).2.2.2
  unfold potential
  omega

theorem completeCountResidues : Targets.CompleteCountResidues := by
  intro f B hf m lam t hm ha hl ht
  have hbase := count_endpoint_facts f B hf lam t ha hl (by omega)
  have horbit := endpoint_potential f B hf m lam t hm ha hl ht
  have heven := endpoint_even_cast f B hf lam t ha hl (by omega)
  have hJ : (headCollapse f lam t : Int) =
      (completeEndpoint f lam t : Int) + (completeCount f lam t : Int) := by
    exact_mod_cast hbase.2.1
  constructor
  · intro hhigh
    obtain ⟨i, _, _, hcount⟩ := highHeadFunnel f B hf lam t ha hl hhigh (by omega)
    have hi := selected_orbit f B hf m t (i + 1) hm (by omega)
    rw [Function.iterate_succ_apply'] at hi
    have hd : Int.ModEq (m : Int) (completeCount f lam t : Int) (potential t : Int) := by
      have h := hi.add_left ((i : Int) + 1)
      have hc : (completeCount f lam t : Int) = (i : Int) + 1 + (potential (f (f^[i] t)) : Int) := by
        exact_mod_cast hcount
      rw [hc]
      convert h using 1 <;> simp only [Int.natCast_add, Int.natCast_one] <;> omega
    have hpzero : Int.ModEq (m : Int) (potential (completeEndpoint f lam t) : Int) 0 := by
      have h := hd.sub_left (potential t : Int)
      have hz : (potential t : Int) - (potential t : Int) = 0 := by omega
      rw [hz] at h
      exact horbit.trans h
    have hz : Int.ModEq (2 * (m : Int)) (completeEndpoint f lam t : Int) 0 := by
      have h := hpzero.mul_left' (c := 2)
      simpa only [← heven, mul_zero] using h
    have hzsmall : Int.ModEq (m : Int) (completeEndpoint f lam t : Int) 0 :=
      hz.of_dvd (dvd_mul_left _ _)
    have hj := hzsmall.add hd
    rw [← hJ] at hj
    exact ⟨hd, hz, by simpa using hj⟩
  · intro k hk
    have had := selected_threshold_admissible f B hf
    have hc : completeCount f lam t = k := by
      unfold completeCount countInitial
      rw [hk]
      exact (finiteCoefficientTerminal f had.1 had.2 k (t - actualOrdinalNorm (Ordinal.omega0 * (k : Ordinal)))).1
    have hz : Int.ModEq (2 * (m : Int)) (completeEndpoint f lam t : Int)
        (2 * (potential t : Int) - 2 * (k : Int)) := by
      rw [hc] at horbit
      have h := horbit.mul_left' (c := 2)
      rw [heven]
      convert h using 1 <;> omega
    have hzsmall := hz.of_dvd (show (m : Int) ∣ 2 * (m : Int) from dvd_mul_left _ _)
    have hj := hzsmall.add_right (k : Int)
    have heq : (headCollapse f lam t : Int) = (completeEndpoint f lam t : Int) + (k : Int) := by
      rw [hJ, hc]
    refine ⟨hc, hz, ?_⟩
    rw [heq]
    convert hj using 1 <;> omega

theorem completeCountTable : Targets.CompleteCountTable := by
  intro f B hf m lam t hm ha hl hhigh ht
  have h := ((completeCountResidues f B hf m lam t hm ha hl ht).1 hhigh).2.2
  have hn := Int.natCast_modEq_iff.mp h
  change headCollapse f lam t % m = potential t % m at hn
  rw [hn, Nat.mod_mul_right_div_self, Nat.mod_mod]
  rfl

end LogicLineages.PermittedControl
