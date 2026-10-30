module
public import LogicLineages.OrdinalComparison.ConstantCutPeriodTargets
public import LogicLineages.OrdinalComparison.CompatiblePrefixFactsProof
public import LogicLineages.OrdinalComparison.RestrictedPartitionPeriodProof
public import LogicLineages.OrdinalComparison.PolynomialOrdinalNormalProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualFiniteMonomialFacts : Targets.ActualFiniteMonomialFacts := by
  intro d k
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, mul_zero, Nat.mul_zero]
    have hz := normalRepresentationSound (NONote.ofNat 0)
    have hn := actualOrdinalNorm_notationCorrespondence (NONote.ofNat 0)
    simp only [NONote.ofNat, ONote.repr_ofNat, Nat.cast_zero, norm_ofNat] at hz hn
    refine ⟨hz, hn, ?_⟩
    intro p hp
    simp only [Ordinal.CNF.zero_right, List.not_mem_nil] at hp
  · let r : NONote := ⟨ONote.oadd (ONote.ofNat d) ⟨k, Nat.pos_of_ne_zero hk⟩ 0,
      ONote.NF.oadd (ONote.nf_ofNat d) _ (ONote.NF.below_of_lt' (Ordinal.opow_pos _ Ordinal.omega0_pos) ONote.NF.zero)⟩
    have heq : r.1.repr = Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal) := by
      change Ordinal.omega0 ^ (ONote.ofNat d).repr * (k : Ordinal) + 0 = _
      rw [ONote.repr_ofNat, add_zero]
    have hs : Ordinal.omega0 ^ (d : Ordinal) * (k : Ordinal) < epsilonZero := by
      rw [← heq]
      exact normalRepresentationSound r
    refine ⟨hs, ?_, ?_⟩
    · rw [← heq, actualOrdinalNorm_notationCorrespondence r]
      change k * (1 + Vendor.R1.treeWeight (ONote.ofNat d)) + 0 = _
      have hn : Vendor.R1.treeWeight (ONote.ofNat d) = d := norm_ofNat d
      rw [hn]
      simp only [Nat.add_zero, Nat.zero_add, Nat.add_comm, Nat.mul_comm]
    · apply (actualMinExponentDivisibility _ hs _).mpr
      exact dvd_mul_right _ _

theorem polynomialRawNoteLeadingDecomposition : Targets.PolynomialRawNoteLeadingDecomposition := by
  intro d a
  by_cases hc : a (Fin.last d) = 0
  · rw [polynomialRawNote, dif_pos hc, hc, Nat.cast_zero, mul_zero, zero_add]
  · rw [polynomialRawNote, dif_neg hc]
    change Ordinal.omega0 ^ (ONote.ofNat d).repr * (a (Fin.last d) : Ordinal) + _ = _
    rw [ONote.repr_ofNat]

theorem restrictedPartitionPeriodDivisibility : Targets.RestrictedPartitionPeriodDivisibility := by
  intro i d m hi hid
  unfold restrictedPartitionPeriod
  exact Nat.mul_dvd_mul (Nat.factorial_dvd_factorial hid) (pow_dvd_pow m (by omega : i - 1 ≤ d - 1))

theorem restrictedPartitionPeriodMultiple : Targets.RestrictedPartitionPeriodMultiple := by
  intro d m n k hd hm
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.ModEq.refl _
  | succ k ih =>
    have h := restrictedPartitionSufficientPeriod d m hd hm (n + restrictedPartitionPeriod d m * k)
    simpa only [Nat.mul_succ, Nat.add_assoc] using h.trans ih

end LogicLineages.OrdinalComparison
