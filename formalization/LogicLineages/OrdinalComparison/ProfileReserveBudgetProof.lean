module
public import LogicLineages.OrdinalComparison.ProfileReserveBudgetTargets
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualProfileLeadingMonomialCorrect : Targets.ActualProfileLeadingMonomial := by
  intro rho hl
  rcases rho with ⟨o, ho⟩
  cases o with
  | zero => exact False.elim ((ne_of_gt hl.bot_lt) rfl)
  | oadd e n tail =>
    have hdiv := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
    have hep : 0 < e.repr := pos_iff_ne_zero.mpr (ho.of_dvd_omega0 hdiv).1
    have hle := ONote.omega0_le_oadd e n tail
    have heps := hle.trans_lt (normalRepresentationSound ⟨ONote.oadd e n tail, ho⟩)
    letI := ho.fst
    let p : NONote := ⟨ONote.oadd e 1 0, inferInstance⟩
    have hn := actualOrdinalNorm_notationCorrespondence p
    refine ⟨e.repr, hep, rfl, hle, heps, ?_⟩
    simpa [p, ONote.repr, Vendor.R1.treeWeight, actualProfileLeadingMonomial, profileLeadingWeight] using hn

theorem actualProfileReserveEligibility : Targets.ActualProfileReserveEligibility := by
  intro beta hb he rho hl hlead
  rcases rho with ⟨o, ho⟩
  cases o with
  | zero => exact False.elim ((ne_of_gt hl.bot_lt) rfl)
  | oadd e n tail =>
    change Ordinal.omega0 ^ e.repr ≤ Ordinal.omega0 ^ beta at hlead
    have hsmall : (ONote.oadd e n tail).repr <
        Ordinal.omega0 ^ e.repr * ((n.val + 1 : Nat) : Ordinal) := by
      simpa only [ONote.repr, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
        add_lt_add_right ho.snd'.repr_lt (Ordinal.omega0 ^ e.repr * (n.val : Ordinal))
    have hn := actualOrdinalNorm_notationCorrespondence ⟨ONote.oadd e n tail, ho⟩
    have hweight : n.val ≤ actualOrdinalNorm (ONote.oadd e n tail).repr := by
      rw [hn]
      change n.val ≤ n.val * (1 + Vendor.R1.treeWeight e) + Vendor.R1.treeWeight tail
      exact (Nat.le_mul_of_pos_right n.val (by omega)).trans (Nat.le_add_right _ _)
    apply hsmall.trans_le
    apply (mul_le_mul_right' hlead (((n.val + 1 : Nat)) : Ordinal)).trans
    apply mul_le_mul_left'
    exact_mod_cast Nat.add_le_add_right hweight 1

theorem actualProfileReserveBudgetCalibration : Targets.ActualProfileReserveBudgetCalibration := by
  intro word hv
  constructor
  · unfold profileReserveBlocks
    congr 1
    apply List.map_congr_left
    intro rho _
    rw [actualOrdinalNorm_notationCorrespondence rho]
  · unfold profileReserveLeadingBound
    congr 1
    apply List.map_congr_left
    intro rho hr
    exact (actualProfileLeadingMonomialCorrect rho (hv rho hr)).choose_spec.2.2.2.2.symm

end LogicLineages.OrdinalComparison
