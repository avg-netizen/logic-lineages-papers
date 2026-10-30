module
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof
public import LogicLineages.OrdinalComparison.NumericalFixedBudgetProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem compatible_prefix_boundary (k r : Ordinal) (hr : r < epsilonZero)
    (hnon : Ordinal.omega0 ≤ r) (hcompat : actualCNFPrefixCompatible k r) :
    ∃ e : Ordinal, 0 < e ∧ actualMinExponentAtLeast k e ∧ r < Ordinal.omega0 ^ (e + 1) := by
  obtain ⟨rn, hrn⟩ := normalRepresentationComplete r hr
  rcases rn with ⟨raw, hnf⟩
  cases raw with
  | zero =>
    rw [← hrn] at hnon
    change Ordinal.omega0 ≤ 0 at hnon
    exact False.elim ((not_le_of_gt Ordinal.omega0_pos) hnon)
  | oadd f c t =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd f c t).repr =
        (f.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt
    have hhead : (f.repr, ((c : Nat) : Ordinal)) ∈ Ordinal.CNF Ordinal.omega0 r := by
      rw [← hrn, hcnf]
      exact List.mem_cons_self
    have hmin : actualMinExponentAtLeast k f.repr := fun p hp => hcompat p hp _ hhead
    have hbound : r < Ordinal.omega0 ^ (f.repr + 1) := by
      rw [← hrn]
      exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt
        (Order.lt_add_one_iff.mpr le_rfl)
    have hne : f.repr ≠ 0 := by
      intro hz
      rw [hz, zero_add, Ordinal.opow_one] at hbound
      exact (not_lt_of_ge hnon) hbound
    exact ⟨f.repr, lt_of_le_of_ne zero_le hne.symm, hmin, hbound⟩

private theorem count_pos_nonfinite (g : Nat → Nat) (r : Ordinal) (hr : r < epsilonZero)
    (hnon : Ordinal.omega0 ≤ r) : 0 < actualControlledCount g r := by
  have hc := (actualControlledCountRecursion g r hr).2 hnon
  omega

theorem actualCompatiblePrefixFirstFiniteCut : Targets.ActualCompatiblePrefixFirstFiniteCut := by
  intro k r hk hr hlim hcompat
  dsimp only
  let g := compensatedPrefixControl (actualOrdinalNorm k)
  let C := actualControlledCount g r
  obtain ⟨e, he, hmin, hbound⟩ := compatible_prefix_boundary k r hr
    (Ordinal.omega0_le_of_isSuccLimit hlim) hcompat
  have hbudget : ∀ n : Nat, actualOrdinalNorm k ≤ Phi (actualOrdinalNorm k + n) := by
    intro n
    exact (Nat.le_add_right _ _).trans (self_lt_Phi _).le
  have ht := actualPrefixControlTrace Phi k r hk hr e he hmin hbound hbudget
  dsimp only at ht
  have hg : prefixRemainderControl Phi (actualOrdinalNorm k) = g := rfl
  rw [hg] at ht
  have hpos : 0 < C := count_pos_nonfinite g r hr (Ordinal.omega0_le_of_isSuccLimit hlim)
  refine ⟨hpos, ht.1, ?_, ht.2.2⟩
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ht.2.1
  exact ⟨n, (ht.1 C le_rfl).trans (congrArg (fun x : Ordinal => k + x) hn)⟩

theorem actualRetainedPrefixFixedBudgetCount : Targets.ActualRetainedPrefixFixedBudgetCount := by
  intro k hk d S n hd hmin hS hN
  dsimp only
  let c := actualOrdinalNorm k
  let r := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
  let C := restrictedPartitionCount d (S - c)
  have he : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hlam : Order.IsSuccLimit (Ordinal.omega0 ^ (d : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt he)
  have hrε : r < epsilonZero :=
    (actualFiniteTailClosureNorm _ (finiteOmegaPowerBelowEpsilonZero d) n).1
  have hrnon : Ordinal.omega0 ≤ r :=
    (Ordinal.omega0_le_of_isSuccLimit hlam).trans le_self_add
  have htail : (n : Ordinal) < Ordinal.omega0 ^ (d : Ordinal) :=
    (Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.omega0_le_of_isSuccLimit hlam)
  have hrbound : r < Ordinal.omega0 ^ ((d : Ordinal) + 1) := by
    have h := Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 1) htail
      (Order.lt_add_one_iff.mpr (le_rfl : (d : Ordinal) ≤ d))
    simpa only [Nat.cast_one, mul_one] using h
  have hbudget : ∀ v : Nat, c ≤ (fun _ => S) (c + v) := by intro _; dsimp [c]; omega
  have ht := actualPrefixControlTrace (fun _ => S) k r hk hrε (d : Ordinal) he hmin hrbound hbudget
  dsimp only at ht
  have hg : prefixRemainderControl (fun _ => S) (actualOrdinalNorm k) = (fun _ => S - c) := rfl
  rw [hg] at ht
  have hc : actualControlledCount (fun _ => S - c) r = C :=
    actualNumericalFixedBudgetPartitionCount d c S n hd hS hN
  rw [hc] at ht
  have hpos := count_pos_nonfinite (fun _ => S - c) r hrε hrnon
  rw [hc] at hpos
  refine ⟨hpos, ht.1, ?_, ht.2.2⟩
  obtain ⟨t, htf⟩ := Ordinal.lt_omega0.mp ht.2.1
  exact ⟨t, (ht.1 C le_rfl).trans (congrArg (fun x : Ordinal => k + x) htf)⟩

theorem fullActualCompatiblePrefixSplitting : Targets.FullActualCompatiblePrefixSplitting :=
  ⟨actualCompatiblePrefixMaximum, compensatedPrefixControlBounds, actualCompatiblePrefixFirstFiniteCut⟩

theorem fullActualFixedBudgetPartitionCount : Targets.FullActualFixedBudgetPartitionCount :=
  ⟨actualNumericalFixedBudgetPartitionCount, actualRetainedPrefixFixedBudgetCount⟩

end LogicLineages.OrdinalComparison
