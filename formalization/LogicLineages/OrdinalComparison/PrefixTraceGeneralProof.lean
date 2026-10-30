module
public import LogicLineages.OrdinalComparison.PrefixTraceBasicProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixMaximumProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualPrefixControlStep : Targets.ActualPrefixControlStep := by
  intro h k r hk hr hnon e he hmin hbound hbudget
  have hdiv := (actualMinExponentDivisibility k hk e).mp hmin
  have hone : (1 : Ordinal) ≤ e := Order.one_le_iff_pos.mpr he
  have homega : Ordinal.omega0 ∣ k := by
    simpa only [Ordinal.opow_one] using (Ordinal.opow_dvd_opow Ordinal.omega0 hone).trans hdiv
  have hnorm := (actualDivisiblePrefixNormAddition k r hk hr e hdiv hbound).2
  have hd := actualNonfiniteDecomposition r hnon hr
  have hlimbound : actualLimitPart r < Ordinal.omega0 ^ (e + 1) :=
    (Ordinal.mul_div_le r Ordinal.omega0).trans_lt hbound
  change actualMaximumPredecessor (actualLimitPart (k + r)) (h (actualOrdinalNorm (k + r))) =
    k + actualMaximumPredecessor (actualLimitPart r)
      (h (actualOrdinalNorm k + actualOrdinalNorm r) - actualOrdinalNorm k)
  rw [actualLimitPartPrefixAddition k homega r, hnorm]
  exact actualDivisiblePrefixMaximum k (actualLimitPart r) hk hd.1 hd.2.1.bot_lt e hmin hlimbound
    _ hbudget

theorem actualPrefixControlTrace : Targets.ActualPrefixControlTrace := by
  intro h k r hk hr e he hmin hbound hbudget
  dsimp only
  let g := prefixRemainderControl h (actualOrdinalNorm k)
  let C := actualControlledCount g r
  have ht := actualControlledTraceFirstFinite g r hr
  have htrace : ∀ i : Nat, i ≤ C →
      actualControlledStateAfter h (k + r) i = k + actualControlledStateAfter g r i := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [actualControlledStateAfter_zero, actualControlledStateAfter_zero]
    | succ i ih =>
      intro hi
      have hpre : i < C := by omega
      have hs := ht.2 i hpre.le
      have hstep := actualPrefixControlStep h k (actualControlledStateAfter g r i)
        hk hs.1 (hs.2.2 hpre) e he hmin (hs.2.1.trans_lt hbound)
        (hbudget (actualOrdinalNorm (actualControlledStateAfter g r i)))
      rw [actualControlledStateAfter_succ, actualControlledStateAfter_succ, ih hpre.le]
      exact hstep
  refine ⟨htrace, ht.1, ?_⟩
  intro i hi
  rw [htrace i hi.le]
  exact add_le_add_right ((ht.2 i hi.le).2.2 hi) k

end LogicLineages.OrdinalComparison
