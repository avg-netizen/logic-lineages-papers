module
public import LogicLineages.OrdinalComparison.ConstantBudgetTargets
public import LogicLineages.OrdinalComparison.ActualCollapseBounds

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualExactNormPredecessorsMembership : Targets.ActualExactNormPredecessorsMembership := by
  classical
  intro a ha b x
  simp only [actualExactNormPredecessors, actualBoundedPredecessors,
    Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h.1.2, h.2⟩,
    fun h => ⟨⟨⟨h.1.trans ha, h.2.le⟩, h.1⟩, h.2⟩⟩

private theorem actual_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  have h := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
  rw [norm_ofNat] at h
  change actualOrdinalNorm (ONote.ofNat n).repr = n at h
  simpa only [ONote.repr_ofNat] using h

/-- Equal norm forbids a strict drop within a single finite-tail interval. -/
theorem actualEqualNormBelowLimitPart : Targets.ActualEqualNormBelowLimitPart := by
  intro x y hy hxy hnorm
  by_cases hf : y < Ordinal.omega0
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hf
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp (hxy.trans hf)
    rw [actual_nat_norm, actual_nat_norm] at hnorm
    have hkn : k < n := by exact_mod_cast hxy
    omega
  · have hn := le_of_not_gt hf
    have hd := actualNonfiniteDecomposition y hn hy
    by_contra hnot
    have hle : actualLimitPart y ≤ x := le_of_not_gt hnot
    have hleft : actualLimitPart y + (x - actualLimitPart y) < y :=
      (Ordinal.add_sub_cancel_of_le hle).trans_lt hxy
    have hleft' := hleft.trans_eq hd.2.2.1
    have hdelta : x - actualLimitPart y < (actualTailPart y : Ordinal) :=
      (add_lt_add_iff_left _).mp hleft'
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (hdelta.trans (Ordinal.natCast_lt_omega0 _))
    have hrepr : actualLimitPart y + (k : Ordinal) = x := by
      rw [← hk]
      exact Ordinal.add_sub_cancel_of_le hle
    have hxnorm := (actualFiniteTailClosureNorm (actualLimitPart y) hd.1 k).2
    rw [hrepr] at hxnorm
    have hkn : k < actualTailPart y := by rw [hk] at hdelta; exact_mod_cast hdelta
    have hynorm := hd.2.2.2
    omega

end LogicLineages.OrdinalComparison
