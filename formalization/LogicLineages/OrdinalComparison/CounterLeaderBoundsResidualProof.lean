module
public import LogicLineages.OrdinalComparison.CounterLeaderBoundsTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionEntriesProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderBounds.Proof
open CounterLeaderExpansion

/-! Each actual count pays for at least that many increases of the numerical
control. The residual list therefore telescopes without any tail assumption.
Its cubic final entry supplies the strict lower correction on the stated tail. -/

private theorem iterate_count_bound (k t : Nat) : t+k ≤ Phi^[k] t := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hs := self_lt_Phi (Phi^[k] t)
    omega

private theorem kernel_count_bound (h c t : Nat) :
    t + count h c t ≤ kernel h c t := by
  change t + count h c t ≤ Phi^[count h c t] t
  exact iterate_count_bound _ _

private theorem residual_sum_succ (n c t : Nat) :
    (residuals (n+1) c t).sum =
      count (n+4) (c+n+4) t +
        (residuals n c (kernel (n+4) (c+n+4) t)).sum := by
  simp only [residuals, entries, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem actualResidualSumBound (n c t : Nat) :
    t + (residuals n c t).sum ≤ leaderPreimage n c t := by
  induction n generalizing t with
  | zero =>
    simpa only [leaderPreimage, bottomInput, residuals, entries,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      using kernel_count_bound 3 (c+3) t
  | succ n ih =>
    let u := kernel (n+4) (c+n+4) t
    have hk : t + count (n+4) (c+n+4) t ≤ u := kernel_count_bound _ _ _
    have hi := ih u
    have hleader : leaderPreimage (n+1) c t = leaderPreimage n c u := rfl
    rw [residual_sum_succ, hleader]
    change t + (count (n+4) (c+n+4) t + (residuals n c u).sum) ≤ _
    omega

private theorem bottom_count_le_sum (n c t : Nat) :
    count 3 (c+3) (bottomInput n c t) ≤ (residuals n c t).sum := by
  induction n generalizing t with
  | zero =>
    simp only [bottomInput, residuals, entries, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    exact le_rfl
  | succ n ih =>
    have hi := ih (kernel (n+4) (c+n+4) t)
    rw [residual_sum_succ]
    change count 3 (c+3) (bottomInput n c (kernel (n+4) (c+n+4) t)) ≤ _
    omega

private theorem cubic_count_large (c a : Nat) (ha : 2*c+10 ≤ a) :
    (c+1)/2 < count 3 (c+3) a := by
  let u := kernel 3 (c+6) a
  have hu : a ≤ u := CounterLeaderExpansion.Proof.kernel_ge _ _ _
  have hb := (CounterLeaderExpansion.Proof.block 1 (c+3) a (by omega)).1
  change count 3 (c+3) a = count 2 (c+3) u + count 3 (c+6) a at hb
  have hq := CounterLeaderExpansion.Proof.quadraticCount (c+3) u (by omega)
  change count 2 (c+3) u = Phi u / 2 - (c+3+1)/2 + 1 at hq
  have hPhi := self_lt_Phi u
  omega

theorem actualResidualBounds : Targets.ActualResidualBounds := by
  refine ⟨actualResidualSumBound, ?_⟩
  intro n c t ht
  have htail : 2*c+10 ≤ t := (le_max_right _ _).trans ht
  have ha := CounterLeaderExpansion.Proof.bottomInput_ge n c t
  exact (cubic_count_large c (bottomInput n c t) (by omega)).trans_le
    (bottom_count_le_sum n c t)

end LogicLineages.OrdinalComparison.CounterLeaderBounds.Proof
