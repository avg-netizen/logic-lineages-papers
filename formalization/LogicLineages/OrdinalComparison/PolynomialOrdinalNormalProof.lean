module
public import LogicLineages.OrdinalComparison.PolynomialOrdinalTargets
public import LogicLineages.OrdinalComparison.RestrictedPartitionCountProof
public import LogicLineages.OrdinalComparison.NormBalls

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem restrictedPartitionWeight_init (d : Nat) (a : Fin (d + 1) → Nat) :
    restrictedPartitionWeight a = restrictedPartitionWeight (Fin.init a) + (d + 1) * a (Fin.last d) := by
  unfold restrictedPartitionWeight
  rw [Fin.sum_univ_castSucc]
  rfl

theorem polynomialRawNoteNormalBoundNorm : Targets.PolynomialRawNoteNormalBoundNorm := by
  intro d
  induction d with
  | zero =>
    intro a
    refine ⟨ONote.NF.zero, Ordinal.opow_pos _ Ordinal.omega0_pos, ?_⟩
    simp only [polynomialRawNote, Vendor.R1.treeWeight, restrictedPartitionWeight,
      Finset.univ_eq_empty, Finset.sum_empty]
  | succ d ih =>
    intro a
    have ht := ih (Fin.init a)
    have hdn : ONote.NF (ONote.ofNat d) := ONote.nf_ofNat d
    have hdweight : Vendor.R1.treeWeight (ONote.ofNat d) = d := norm_ofNat d
    have hweight := restrictedPartitionWeight_init d a
    by_cases hc : a (Fin.last d) = 0
    · simp only [polynomialRawNote, dif_pos hc]
      refine ⟨ht.1, ht.2.1.trans_le ?_, ?_⟩
      · exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone
          (by exact_mod_cast Nat.le_succ d)
      · have hw0 : restrictedPartitionWeight a = restrictedPartitionWeight (Fin.init a) := by
          simpa only [hc, Nat.mul_zero, Nat.add_zero] using hweight
        exact ht.2.2.trans hw0.symm
    · simp only [polynomialRawNote, dif_neg hc]
      refine ⟨hdn.oadd _ (ONote.NF.below_of_lt' ?_ ht.1), ?_, ?_⟩
      · simpa only [ONote.repr_ofNat] using ht.2.1
      · change Ordinal.omega0 ^ (ONote.ofNat d).repr * (a (Fin.last d) : Ordinal) +
          (polynomialRawNote d (Fin.init a)).repr < _
        rw [ONote.repr_ofNat]
        exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) ht.2.1
          (by exact_mod_cast Nat.lt_succ_self d)
      · change a (Fin.last d) * (1 + Vendor.R1.treeWeight (ONote.ofNat d)) +
          Vendor.R1.treeWeight (polynomialRawNote d (Fin.init a)) = _
        rw [hdweight, ht.2.2, hweight]
        simp only [Nat.add_comm, Nat.mul_comm]

end LogicLineages.OrdinalComparison
