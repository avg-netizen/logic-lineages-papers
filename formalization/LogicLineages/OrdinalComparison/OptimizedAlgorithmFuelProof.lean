module
public import LogicLineages.OrdinalComparison.OptimizedAlgorithmTargets
public import LogicLineages.OrdinalComparison.OptimizedMaximumBranchesProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem raw_repr_pos (a : ONote) (ha : a ≠ 0) : 0 < a.repr := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | oadd e c r => exact ONote.oadd_pos e c r

private theorem raw_repr_zero_iff (a : ONote) : a.repr = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hn
    exact (ne_of_gt (raw_repr_pos a hn)) h
  · rintro rfl
    rfl

private theorem optimizedRawBlock_properties (e r : ONote) (he : ONote.NF e)
    (hr : ONote.NF r) (hlt : r.repr < Ordinal.omega0 ^ e.repr) (c : Nat) :
    ONote.NF (optimizedRawBlock e c r) ∧
      (optimizedRawBlock e c r).repr = Ordinal.omega0 ^ e.repr * (c : Ordinal) + r.repr := by
  by_cases hc : c = 0
  · simp only [optimizedRawBlock, dif_pos hc, hc, Nat.cast_zero, mul_zero, zero_add]
    exact ⟨hr, rfl⟩
  · simp only [optimizedRawBlock, dif_neg hc, ONote.repr]
    exact ⟨he.oadd _ (ONote.NF.below_of_lt' hlt hr), rfl⟩

theorem optimizedMaximumFuelCorrect : Targets.OptimizedMaximumFuelCorrect := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro a b h
      unfold optimizedMaximumRank at h
      omega
    · intro e b h
      unfold optimizedMaximumRank at h
      omega
  | succ fuel ih =>
    constructor
    · intro a b hrank hapos
      by_cases hb : b = 0
      · simp only [optimizedRawMaximumFuel, if_pos hb]
        refine ⟨ONote.NF.zero, ?_⟩
        simpa only [ONote.repr_zero, hb] using
          (actualOptimizedMaximumBaseCases.1 a.1.repr hapos (normalRepresentationSound a)).symm
      · rcases a with ⟨raw, hnf⟩
        cases raw with
        | zero => exact False.elim ((not_lt_of_ge (le_refl 0)) hapos)
        | oadd e c r =>
          have hen := actualOrdinalNorm_notationCorrespondence (⟨e, hnf.fst⟩ : NONote)
          change actualOrdinalNorm e.repr = Vendor.R1.treeWeight e at hen
          have heε := normalRepresentationSound (⟨e, hnf.fst⟩ : NONote)
          have hrε := normalRepresentationSound (⟨r, hnf.snd⟩ : NONote)
          let w := 1 + Vendor.R1.treeWeight e
          by_cases hkeep : r ≠ 0 ∧ (c : Nat) * w ≤ b
          · have hcharge : 0 < (c : Nat) * w := Nat.mul_pos c.pos (by dsimp [w]; omega)
            have hdec := optimizedMaximumCallsDecrease.1 b ((c : Nat) * w) hcharge hkeep.2
            have hcall : optimizedMaximumRank (b - (c : Nat) * w) 1 < fuel := by
              unfold optimizedMaximumRank at *
              omega
            have hir := ih.1 (⟨r, hnf.snd⟩ : NONote) (b - (c : Nat) * w) hcall
              (raw_repr_pos r hkeep.1)
            have hmax := actualMaximumPredecessor_correct r.repr (raw_repr_pos r hkeep.1)
              hrε (b - (c : Nat) * w)
            have hout : (optimizedRawMaximumFuel fuel r (b - (c : Nat) * w) true).repr <
                Ordinal.omega0 ^ e.repr := by
              rw [hir.2]
              exact hmax.1.1.trans hnf.snd'.repr_lt
            simp only [optimizedRawMaximumFuel, if_neg hb, show 1 + Vendor.R1.treeWeight e = w from rfl, if_pos hkeep]
            refine ⟨hnf.fst.oadd c (ONote.NF.below_of_lt' hout hir.1), ?_⟩
            have hsource := actualMaximumRetainLeadingBlock e.repr r.repr heε
              hnf.snd'.repr_lt (raw_repr_pos r hkeep.1) (c : Nat) c.pos b
              (by simpa only [hen] using hkeep.2)
            change Ordinal.omega0 ^ e.repr * ((c : Nat) : Ordinal) +
              (optimizedRawMaximumFuel fuel r (b - (c : Nat) * w) true).repr = _
            rw [hir.2, ONote.repr, hsource, hen]
          · let d := min (if r = 0 then (c : Nat) - 1 else (c : Nat)) (b / w)
            have hdec := optimizedMaximumCallsDecrease.2.1 b d w
            have hcall : optimizedMaximumRank (b - d * w) 0 < fuel := by
              unfold optimizedMaximumRank at *
              omega
            have hie := ih.2 (⟨e, hnf.fst⟩ : NONote) (b - d * w) hcall
            have hbound := actualMaximumPredecessor_correct (Ordinal.omega0 ^ e.repr)
              (Ordinal.opow_pos _ Ordinal.omega0_pos)
              ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr heε)
              (b - d * w)
            have hout : (optimizedRawMaximumFuel fuel e (b - d * w) false).repr <
                Ordinal.omega0 ^ e.repr := by rw [hie.2]; exact hbound.1.1
            have hprop := optimizedRawBlock_properties e _ hnf.fst hie.1 hout d
            have hsource := actualMaximumDropLeadingBlock e.repr r.repr heε hnf.snd'.repr_lt
              (c : Nat) c.pos b (by
                rintro ⟨hrpos, hbudget⟩
                apply hkeep
                refine ⟨?_, by simpa only [hen] using hbudget⟩
                intro hrzero
                rw [hrzero, ONote.repr_zero] at hrpos
                exact (not_lt_of_ge (le_refl 0)) hrpos)
            have hd : actualMaximumDropCoefficient e.repr r.repr (c : Nat) b = d := by
              simp only [actualMaximumDropCoefficient, raw_repr_zero_iff, hen]
              rfl
            simp only [optimizedRawMaximumFuel, if_neg hb, show 1 + Vendor.R1.treeWeight e = w from rfl, if_neg hkeep]
            refine ⟨hprop.1, ?_⟩
            change (optimizedRawBlock e d _).repr = _
            rw [hprop.2, hie.2, ONote.repr, hsource, hd, hen]
    · intro e b hrank
      by_cases hbase : b = 0 ∨ e.1 = 0
      · simp only [optimizedRawMaximumFuel, if_pos hbase]
        refine ⟨ONote.NF.zero, ?_⟩
        rcases hbase with hb | hezero
        · simpa only [ONote.repr_zero, hb] using
            (actualOptimizedMaximumBaseCases.2.2 e.1.repr (normalRepresentationSound e)).symm
        · simpa only [hezero, ONote.repr_zero] using
            (actualOptimizedMaximumBaseCases.2.1 b).symm
      · have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hbase (Or.inl hz))
        have hezero : e.1 ≠ 0 := fun hz => hbase (Or.inr hz)
        have hepos : 0 < e.1.repr := raw_repr_pos e.1 hezero
        have heε := normalRepresentationSound e
        have hdec := optimizedMaximumCallsDecrease.2.2.1 b hb
        have hcall : optimizedMaximumRank (b - 1) 1 < fuel := by
          unfold optimizedMaximumRank at *
          omega
        have hia := ih.1 e (b - 1) hcall hepos
        let a := optimizedRawMaximumFuel fuel e.1 (b - 1) true
        have han := actualOrdinalNorm_notationCorrespondence (⟨a, hia.1⟩ : NONote)
        change actualOrdinalNorm a.repr = Vendor.R1.treeWeight a at han
        have hamax := actualMaximumPredecessor_correct e.1.repr hepos heε (b - 1)
        have habudget : Vendor.R1.treeWeight a ≤ b - 1 := by
          have h := hamax.1.2
          rw [← hia.2, han] at h
          exact h
        let v := 1 + Vendor.R1.treeWeight a
        have hv : v ≤ b := by dsimp [v]; omega
        have hvpos : 0 < v := by dsimp [v]; omega
        have hmod := Nat.mod_lt b hvpos
        have htailcall : optimizedMaximumRank (b % v) 0 < fuel := by
          unfold optimizedMaximumRank at *
          omega
        have hit := ih.2 (⟨a, hia.1⟩ : NONote) (b % v) htailcall
        have haε := normalRepresentationSound (⟨a, hia.1⟩ : NONote)
        have htail := actualMaximumPredecessor_correct (Ordinal.omega0 ^ a.repr)
          (Ordinal.opow_pos _ Ordinal.omega0_pos)
          ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr haε)
          (b % v)
        have hout : (optimizedRawMaximumFuel fuel a (b % v) false).repr < Ordinal.omega0 ^ a.repr := by
          rw [hit.2]
          exact htail.1.1
        have hprop := optimizedRawBlock_properties a _ hia.1 hit.1 hout (b / v)
        have hsource := actualLowerPowerGreedyRecurrence e.1.repr hepos heε b hb
        dsimp only at hsource
        rw [← hia.2, han] at hsource
        simp only [optimizedRawMaximumFuel, if_neg hbase]
        refine ⟨hprop.1, ?_⟩
        change (optimizedRawBlock a (b / v) (optimizedRawMaximumFuel fuel a (b % v) false)).repr = _
        rw [hprop.2, hit.2]
        exact hsource.symm

end LogicLineages.OrdinalComparison
