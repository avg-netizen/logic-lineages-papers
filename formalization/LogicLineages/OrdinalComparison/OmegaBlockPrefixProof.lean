module
public import LogicLineages.OrdinalComparison.OmegaBlockNumericalProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualRetainedPrefixOmegaBlock : Targets.ActualRetainedPrefixOmegaBlock := by
  intro k hk hmin u m hu hm hBlarge hmB
  dsimp only
  let c := actualOrdinalNorm k
  let a := actualHeadInitial (Ordinal.omega0 ^ Ordinal.omega0) (u - c)
  let H := actualOmegaCopyCount c u
  have hOmega := actualOmegaOmegaFacts
  have hi := actualHeadInputFacts _ hOmega.1 hOmega.2.1 (u - c) (by rw [hOmega.2.2]; omega)
  have habound : a < Ordinal.omega0 ^ (Ordinal.omega0 + 1) := by
    have htail : ((u - c - actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0) : Nat) : Ordinal) <
        Ordinal.omega0 ^ Ordinal.omega0 :=
      (Ordinal.natCast_lt_omega0 _).trans_le (Ordinal.omega0_le_of_isSuccLimit hOmega.2.1)
    have h := Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 1) htail
      (Order.lt_add_one_iff.mpr (le_rfl : Ordinal.omega0.{0} ≤ Ordinal.omega0))
    simpa only [a, actualHeadInitial, Nat.cast_one, mul_one] using h
  have hbudget : ∀ n : Nat, actualOrdinalNorm k ≤ Phi (actualOrdinalNorm k + n) := by
    intro n
    exact (Nat.le_add_right _ _).trans (self_lt_Phi _).le
  have ht := actualPrefixControlTrace Phi k a hk hi.1 Ordinal.omega0 Ordinal.omega0_pos
    hmin habound hbudget
  dsimp only at ht
  have hg : prefixRemainderControl Phi (actualOrdinalNorm k) = compensatedPrefixControl c := rfl
  rw [hg] at ht
  have hn := actualNumericalOmegaBlock c u m hu hm hBlarge hmB
  have hdecomp := actualRetainedPrefixCountDecomposition Phi k a hk hi.1 Ordinal.omega0
    Ordinal.omega0_pos hmin habound hbudget
  dsimp only at hdecomp
  rw [hg] at hdecomp
  have hle : H ≤ actualControlledCount Phi (k + a) := hdecomp.1
  have hdiv := (actualMinExponentDivisibility k hk Ordinal.omega0).mp hmin
  have hsum := actualDivisiblePrefixNormAddition k a hk hi.1 Ordinal.omega0 hdiv habound
  have hinitnorm : actualOrdinalNorm (k + a) = u := by
    rw [hsum.2, hi.2.2]
    exact Nat.add_sub_of_le (by omega : actualOrdinalNorm k ≤ u)
  have hnorm := actualControlledNormIteration Phi (k + a) hsum.1 H hle
  rw [hinitnorm] at hnorm
  refine ⟨hn.1, ht.1, ?_, ht.2.2, hnorm⟩
  obtain ⟨n, hfinite⟩ := Ordinal.lt_omega0.mp ht.2.1
  exact ⟨n, (ht.1 H le_rfl).trans (congrArg (fun x : Ordinal => k + x) hfinite)⟩

theorem fullActualOmegaBlock : Targets.FullActualOmegaBlock :=
  ⟨actualOmegaOmegaFacts, actualOmegaOmegaMaximum, restrictedPartitionDoubleExponentBound,
    actualOmegaBlockFirstStep, actualNumericalOmegaBlock, actualRetainedPrefixOmegaBlock⟩

end LogicLineages.OrdinalComparison
