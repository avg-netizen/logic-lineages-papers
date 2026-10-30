module
public import LogicLineages.OrdinalComparison.GrowingBudgetNumericalProof
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualLocalRetainedPrefixControlTrace : Targets.ActualLocalRetainedPrefixControlTrace := by
  intro h k r hk hr e he hmin hbound
  dsimp only
  let g := fun i : Nat => h i - actualOrdinalNorm k
  let C := actualScheduledCount g r
  intro hbudget
  have ht := actualScheduledFirstFinite g r hr
  have htrace : ∀ i : Nat, i ≤ C → actualScheduledStateAfter h (k + r) i =
      k + actualScheduledStateAfter g r i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hpre : i < C := by omega
      have hs := ht.2 i hpre.le
      have hstep := actualPrefixControlStep (fun _ => h i) k (actualScheduledStateAfter g r i)
        hk hs.1 (hs.2.2 hpre) e he hmin (hs.2.1.trans_lt hbound) (hbudget i hpre)
      rw [actualScheduledStateLastStep, actualScheduledStateLastStep, ih hpre.le]
      exact hstep
  refine ⟨htrace, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ht.1
    exact ⟨n, (htrace C le_rfl).trans (congrArg (fun x : Ordinal => k + x) hn)⟩
  · intro i hi
    rw [htrace i hi.le]
    exact add_le_add_right ((ht.2 i hi.le).2.2 hi) k

theorem actualRetainedPrefixCongruentBudgetTransfer : Targets.ActualRetainedPrefixCongruentBudgetTransfer := by
  intro d m hd hm k hk hmin S n hS h
  dsimp only
  let c := actualOrdinalNorm k
  let g := fun i : Nat => h i - c
  let a := Ordinal.omega0 ^ (d : Ordinal) + (n : Ordinal)
  let C := actualScheduledCount g a
  intro hlive
  have hmod := actualNumericalCongruentBudgetTransfer d m c S n hd hm hS h hlive
  have hdpos : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ (d : Ordinal)) :=
    Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hdpos)
  have hae : a < epsilonZero :=
    (actualFiniteTailClosureNorm _ (finiteOmegaPowerBelowEpsilonZero d) n).1
  have htail : (n : Ordinal) < Ordinal.omega0 ^ (d : Ordinal) :=
    (Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.omega0_le_of_isSuccLimit hlim)
  have habound : a < Ordinal.omega0 ^ ((d : Ordinal) + 1) := by
    have hb := Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 1) htail
      (Order.lt_add_one_iff.mpr (le_rfl : (d : Ordinal) ≤ d))
    simpa only [Nat.cast_one, mul_one] using hb
  have hbudget : ∀ i : Nat, i < C → actualOrdinalNorm k ≤ h i := by
    intro i hi
    have hbi := (hlive i hi).1
    omega
  have ht := actualLocalRetainedPrefixControlTrace h k a hk hae (d : Ordinal) hdpos hmin habound hbudget
  exact ⟨hmod, ht⟩

theorem fullActualCongruentBudgetTransfer : Targets.FullActualCongruentBudgetTransfer :=
  ⟨actualScheduledFirstFinite, actualScheduledConstantCount, actualConstantBudgetCutPeriod,
    actualConstantBudgetCutCongruence, actualGrowingBudgetCutTransfer, actualNumericalCongruentBudgetTransfer,
    actualLocalRetainedPrefixControlTrace, actualRetainedPrefixCongruentBudgetTransfer⟩

end LogicLineages.OrdinalComparison
