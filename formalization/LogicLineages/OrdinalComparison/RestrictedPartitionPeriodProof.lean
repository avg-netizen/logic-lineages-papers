module
public import LogicLineages.OrdinalComparison.RestrictedPartitionCountProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem modEq_sum_range (m N : Nat) (f g : Nat → Nat)
    (h : ∀ j : Nat, j < N → Nat.ModEq m (f j) (g j)) :
    Nat.ModEq m (∑ j ∈ Finset.range N, f j) (∑ j ∈ Finset.range N, g j) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact Nat.ModEq.refl _
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (ih (fun j hj => h j (Nat.lt_succ_of_lt hj))).add (h N (Nat.lt_succ_self N))

private theorem modEq_period_multiple (m P : Nat) (f : Nat → Nat)
    (h : ∀ n : Nat, Nat.ModEq m (f (n + P)) (f n)) (n k : Nat) :
    Nat.ModEq m (f (n + k * P)) (f n) := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero] using (Nat.ModEq.refl (f n) : Nat.ModEq m (f n) (f n))
  | succ k ih =>
    simpa only [Nat.succ_mul, Nat.add_assoc] using (h (n + k * P)).trans ih

private theorem modEq_periodic_sum_zero (m P : Nat) (f : Nat → Nat)
    (h : ∀ n : Nat, Nat.ModEq m (f (n + P)) (f n)) :
    Nat.ModEq m (∑ j ∈ Finset.range (m * P), f j) 0 := by
  let S := ∑ j ∈ Finset.range P, f j
  have hblocks : ∀ k : Nat, Nat.ModEq m (∑ j ∈ Finset.range (k * P), f j) (k * S) := by
    intro k
    induction k with
    | zero => simp only [Nat.zero_mul, Finset.range_zero, Finset.sum_empty]; exact Nat.ModEq.refl _
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add]
      have hblock : Nat.ModEq m (∑ j ∈ Finset.range P, f (k * P + j)) S := by
        apply modEq_sum_range
        intro j _
        simpa only [Nat.add_comm] using modEq_period_multiple m P f h j k
      simpa only [Nat.succ_mul] using ih.add hblock
  exact (hblocks m).trans (Nat.modEq_zero_iff_dvd.mpr ⟨S, rfl⟩)

/-- One extra part-size step, derived from the actual last-coordinate bijection. -/
theorem restrictedPartitionStepRecurrence (d n : Nat) :
    restrictedPartitionCount (d + 1) (n + (d + 1)) =
      restrictedPartitionCount (d + 1) n + restrictedPartitionCount d (n + (d + 1)) := by
  have hdiv : (n + (d + 1)) / (d + 1) = n / (d + 1) + 1 :=
    Nat.add_div_right _ (Nat.succ_pos d)
  rw [restrictedPartitionLastCoordinateRecurrence d (n + (d + 1)), hdiv,
    Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [restrictedPartitionLastCoordinateRecurrence d n]
  have hshift :
      (∑ j ∈ Finset.range (n / (d + 1) + 1),
        restrictedPartitionCount d (n + (d + 1) - (d + 1) * (j + 1))) =
      ∑ j ∈ Finset.range (n / (d + 1) + 1), restrictedPartitionCount d (n - (d + 1) * j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [Nat.mul_succ, Nat.add_sub_add_right]
  omega

theorem restrictedPartitionStepSum (d n k : Nat) :
    restrictedPartitionCount (d + 1) (n + (d + 1) * k) =
      restrictedPartitionCount (d + 1) n +
        ∑ j ∈ Finset.range k, restrictedPartitionCount d (n + (d + 1) * (j + 1)) := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero, Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, restrictedPartitionStepRecurrence, ih,
      Finset.sum_range_succ]
    simp only [Nat.add_assoc, Nat.mul_succ]

/-- The full source sufficient period, for the actual source cardinalities. -/
theorem restrictedPartitionSufficientPeriod : Targets.RestrictedPartitionSufficientPeriod := by
  intro d m hd hm
  induction d, hd using Nat.le_induction with
  | base =>
    intro n
    rw [restrictedPartitionUnitCount, restrictedPartitionUnitCount]
  | succ d hd ih =>
    intro n
    let P := restrictedPartitionPeriod d m
    let f := fun j : Nat => restrictedPartitionCount d (n + (d + 1) * (j + 1))
    have hseq : ∀ j : Nat, Nat.ModEq m (f (j + P)) (f j) := by
      intro j
      have hp : Nat.ModEq m
          (restrictedPartitionCount d ((n + (d + 1) * (j + 1)) + (d + 1) * P))
          (restrictedPartitionCount d (n + (d + 1) * (j + 1))) :=
        modEq_period_multiple m P (restrictedPartitionCount d) ih _ (d + 1)
      simpa only [f, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hp
    have hsum := modEq_periodic_sum_zero m P f hseq
    have hpow : m ^ d = m * m ^ (d - 1) := by
      have hds : d = d - 1 + 1 := by omega
      conv_lhs => rw [hds, Nat.pow_succ]
      exact Nat.mul_comm _ _
    have hperiod : restrictedPartitionPeriod (d + 1) m = (d + 1) * (m * P) := by
      simp only [P, restrictedPartitionPeriod]
      rw [Nat.add_sub_cancel, Nat.factorial_succ, hpow]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hperiod, restrictedPartitionStepSum]
    simpa only [f, Nat.add_zero] using (Nat.ModEq.refl (restrictedPartitionCount (d + 1) n)).add hsum

theorem fullRestrictedPartitionSufficientPeriod : Targets.FullRestrictedPartitionSufficientPeriod :=
  ⟨restrictedPartitionCoordinateBound, restrictedPartitionFinite,
    restrictedPartitionUnitCount, restrictedPartitionLastCoordinateRecurrence,
    restrictedPartitionSufficientPeriod⟩

end LogicLineages.OrdinalComparison
