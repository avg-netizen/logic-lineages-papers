module
public import LogicLineages.OrdinalComparison.PrincipalBlockDomainTargets
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualPrincipalBlockUpperBound : Targets.ActualPrincipalBlockUpperBound := by
  intro es d hd hbound n
  have hlarge : Ordinal.omega0 ≤ Ordinal.omega0 ^ (d + 1) := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (show (1 : Ordinal) ≤ d + 1 from le_add_self)
  induction es with
  | nil =>
    simpa [principalBlockSum] using (Ordinal.natCast_lt_omega0 n).trans_le hlarge
  | cons e es ih =>
    have hhead : e.repr < d + 1 := (hbound e (by simp)).trans_lt (lt_add_one d)
    have hpow := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hhead
    have htail := ih (fun f hf => hbound f (List.mem_cons_of_mem e hf))
    change (Ordinal.omega0 ^ e.repr + principalBlockSum es) + (n : Ordinal) < _
    rw [add_assoc]
    exact Ordinal.isPrincipal_add_omega0_opow (d + 1) hpow htail

private theorem block_single_facts (e : ONote) (he : ONote.NF e) :
    Ordinal.omega0 ^ e.repr < epsilonZero ∧
      actualOrdinalNorm (Ordinal.omega0 ^ e.repr) = 1 + Vendor.R1.treeWeight e := by
  letI := he
  let o : NONote := ⟨ONote.oadd e 1 0, inferInstance⟩
  have hs := normalRepresentationSound o
  have hn := actualOrdinalNorm_notationCorrespondence o
  constructor
  · simpa [o, ONote.repr] using hs
  · simpa [o, ONote.repr, Vendor.R1.treeWeight] using hn

theorem actualPrincipalBlockSumDomain : Targets.ActualPrincipalBlockSumDomain := by
  intro es
  induction es with
  | nil =>
    intro _
    have hs := normalRepresentationSound ⟨ONote.zero, ONote.NF.zero⟩
    have hn := actualOrdinalNorm_notationCorrespondence ⟨ONote.zero, ONote.NF.zero⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [principalBlockSum, ONote.repr] using hs
    · simpa [principalBlockSum, principalBlocksWeight, ONote.repr, Vendor.R1.treeWeight] using hn
    · simp
  | cons e es ih =>
    intro hg
    have he := hg.1 e (by simp)
    have hpair := List.pairwise_cons.mp hg.2
    have htail : GenuinePrincipalBlocks es :=
      ⟨fun f hf => hg.1 f (List.mem_cons_of_mem e hf), hpair.2⟩
    have hs := ih htail
    have htheta := block_single_facts e he.1
    have hbound : principalBlockSum es < Ordinal.omega0 ^ (e.repr + 1) := by
      simpa only [Nat.cast_zero, add_zero] using
        actualPrincipalBlockUpperBound es e.repr he.2 hpair.1 0
    have hsum := actualDivisiblePrefixNormAddition (Ordinal.omega0 ^ e.repr)
      (principalBlockSum es) htheta.1 hs.1 e.repr (dvd_refl _) hbound
    refine ⟨hsum.1, ?_, ?_⟩
    · change actualOrdinalNorm (Ordinal.omega0 ^ e.repr + principalBlockSum es) = _
      rw [hsum.2, htheta.2, hs.2.1]
      rfl
    · intro _
      change Order.IsSuccLimit (Ordinal.omega0 ^ e.repr + principalBlockSum es)
      by_cases hz : es = []
      · subst es
        simpa [principalBlockSum] using
          Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt he.2)
      · exact Ordinal.isSuccLimit_add _ (hs.2.2 hz)

end LogicLineages.OrdinalComparison
