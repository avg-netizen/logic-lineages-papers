module
public import LogicLineages.OrdinalComparison.AffordableLeadingTargets
public import LogicLineages.OrdinalComparison.ProfileDominatorProof
public import LogicLineages.OrdinalComparison.KernelTransportProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem affordable_leading_facts (o : NONote) (ho : Ordinal.omega0 ≤ o.1.repr) :
    let pi := (profileLeadingNote o).1.repr
    Ordinal.omega0 ≤ pi ∧ pi ≤ o.1.repr ∧ o.1.repr < pi * Ordinal.omega0 ∧
      actualOrdinalNorm pi ≤ actualOrdinalNorm o.1.repr ∧
      (∃ beta : Ordinal.{0}, 0 < beta ∧ pi = Ordinal.omega0 ^ beta) ∧
      ∀ delta : Ordinal.{0}, Ordinal.omega0 ^ delta ≤ o.1.repr → Ordinal.omega0 ^ delta ≤ pi := by
  rcases o with ⟨o, hn⟩
  cases o with
  | zero => exact False.elim ((not_le_of_gt Ordinal.omega0_pos) ho)
  | oadd e n tail =>
    have hep : 0 < e.repr := by
      by_contra hh
      have he : e.repr = 0 := le_antisymm (not_lt.mp hh) zero_le
      have hsmall := (hn.below_of_lt (by rw [he]; exact zero_lt_one : e.repr < 1)).repr_lt
      rw [Ordinal.opow_one] at hsmall
      exact not_lt_of_ge ho hsmall
    have hp : (profileLeadingNote ⟨ONote.oadd e n tail, hn⟩).1.repr = Ordinal.omega0 ^ e.repr := by
      simp [profileLeadingNote, ONote.repr]
    dsimp only
    rw [hp]
    have hnorm := actualOrdinalNorm_notationCorrespondence ⟨ONote.oadd e n tail, hn⟩
    have hleadnorm := actualOrdinalNorm_notationCorrespondence (profileLeadingNote ⟨ONote.oadd e n tail, hn⟩)
    rw [hp] at hleadnorm
    have hbelow := (hn.below_of_lt (Order.lt_add_one_iff.mpr le_rfl)).repr_lt
    rw [Ordinal.opow_add_one] at hbelow
    refine ⟨?_, ONote.omega0_le_oadd e n tail, hbelow, ?_, ⟨e.repr, hep, rfl⟩, ?_⟩
    · simpa only [Ordinal.opow_one] using
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.one_le_iff_pos.mpr hep))
    · rw [hnorm, hleadnorm]
      simp only [profileLeadingNote, Vendor.R1.treeWeight, PNat.one_coe, Nat.one_mul, Nat.add_zero]
      change 1 + Vendor.R1.treeWeight e ≤ n.val * (1 + Vendor.R1.treeWeight e) + Vendor.R1.treeWeight tail
      have hm : 1 + Vendor.R1.treeWeight e ≤ n.val * (1 + Vendor.R1.treeWeight e) := by
        simpa using Nat.mul_le_mul_right (1 + Vendor.R1.treeWeight e) n.pos
      exact hm.trans (Nat.le_add_right _ _)
    · intro delta hd
      have hedelta : delta ≤ e.repr := by
        by_contra hh
        have hx := (hn.below_of_lt (lt_of_not_ge hh)).repr_lt
        exact not_lt_of_ge hd hx
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos hedelta

theorem actualAffordableLeadingMaximum : Targets.ActualAffordableLeadingMaximum := by
  intro L hprincipal hlarge budget hb
  dsimp only
  have he := normalRepresentationSound L
  have hpos : 0 < L := Ordinal.omega0_pos.trans hlarge
  have hm := actualMaximumPredecessor_correct L.1.repr hpos he budget
  have hn := actualMaximumPredecessor_notationCorrespondence L hpos budget
  obtain ⟨ell, hL⟩ := hprincipal
  have hell : 0 < ell := by
    have hh : (1 : Ordinal) < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
      rw [Ordinal.opow_one, ← hL]; exact hlarge)
    exact zero_lt_one.trans hh
  have hl : Order.IsSuccLimit L.1.repr := by
    rw [hL]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hell)
  have hnorm := actualLimitMaximumPredecessorSaturation L.1.repr he hl budget
  have homega : actualOrdinalNorm Ordinal.omega0 = 2 := by
    simpa only [Nat.cast_one, mul_one, Nat.cast_zero, add_zero, Nat.mul_one, Nat.add_zero] using actualFiniteHeadNorm 1 0
  have hnon : Ordinal.omega0 ≤ actualMaximumPredecessor L.1.repr budget := hm.2 ⟨hlarge, by rw [homega]; exact hb⟩
  have hf := affordable_leading_facts (maximumPredecessor L budget) (by rw [hn]; exact hnon)
  rw [hn] at hf
  refine ⟨hn, hnorm, hnon, hf.1, hf.2.1, hf.2.2.1, hf.2.1.trans_lt hm.1.1,
    hf.2.2.2.1.trans_eq hnorm, hf.2.2.2.2.1, ?_⟩
  intro delta hd hdN
  exact hf.2.2.2.2.2 delta (hm.2 ⟨hd, hdN⟩)

end LogicLineages.OrdinalComparison
