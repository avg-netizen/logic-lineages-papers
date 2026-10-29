module
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions
public import LogicLineages.OrdinalComparison.ActualNormRecursionTargets
public import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualOrdinalNorm_cnfEquation : Targets.ActualNormCNFEquation actualOrdinalNorm := by
  intro a ha
  conv_lhs => rw [actualOrdinalNorm, WellFounded.fix_eq]
  simp only [dif_pos ha]
  change ((Ordinal.CNF Ordinal.omega0 a).attach.map
    (fun p => p.1.2.card.toNat * (1 + actualOrdinalNorm p.1.1))).sum = _
  exact congrArg List.sum (List.attach_map_val (f :=
    fun p : Ordinal × Ordinal => p.2.card.toNat * (1 + actualOrdinalNorm p.1)))

theorem actualOrdinalNorm_uniqueBelowEpsilonZero :
    Targets.ActualNormUniqueBelowEpsilonZero actualOrdinalNorm := by
  intro M hM a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro ha
      rw [hM a ha, actualOrdinalNorm_cnfEquation a ha]
      congr 1
      apply List.map_congr_left
      intro p hp
      have hpa := (cnfDescentBelowEpsilonZero a ha p hp).1
      rw [ih p.1 hpa (hpa.trans ha)]

private theorem actualOrdinalNorm_rawCorrespondence (a : ONote) (ha : ONote.NF a) :
    actualOrdinalNorm a.repr = Vendor.R1.treeWeight a := by
  induction a with
  | zero =>
      rw [actualOrdinalNorm_cnfEquation _ (normalRepresentationSound ⟨.zero, ha⟩)]
      simp only [ONote.repr, Ordinal.CNF.zero_right, List.map_nil, List.sum_nil,
        Vendor.R1.treeWeight]
  | oadd e c t ihe iht =>
      have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
      have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd e c t).repr =
          (e.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
        Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
          (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
      rw [actualOrdinalNorm_cnfEquation _ (normalRepresentationSound ⟨_, ha⟩), hcnf]
      simp only [List.map_cons, List.sum_cons, Ordinal.card_nat, Cardinal.toNat_natCast,
        ihe ha.fst, Vendor.R1.treeWeight]
      rw [← actualOrdinalNorm_cnfEquation _ (normalRepresentationSound ⟨t, ha.snd⟩),
        iht ha.snd]

theorem actualOrdinalNorm_notationCorrespondence :
    Targets.ActualNormNotationCorrespondence actualOrdinalNorm :=
  fun a => actualOrdinalNorm_rawCorrespondence a.1 a.2

end LogicLineages.OrdinalComparison
