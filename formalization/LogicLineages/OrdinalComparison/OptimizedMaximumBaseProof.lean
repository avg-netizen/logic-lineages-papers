module
public import LogicLineages.OrdinalComparison.OptimizedMaximumTargets
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor
public import LogicLineages.OrdinalComparison.NormBalls

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem actual_norm_zero (a : Ordinal) (ha : a < epsilonZero)
    (hn : actualOrdinalNorm a = 0) : a = 0 := by
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  have hw : Vendor.R1.treeWeight r.1 = 0 := by
    rw [← actualOrdinalNorm_notationCorrespondence r, hr]
    exact hn
  have hz := (treeWeight_eq_zero_iff r.1).mp hw
  rw [← hr, hz]
  rfl

private theorem actual_maximum_zero_budget (a : Ordinal) (hpos : 0 < a) (ha : a < epsilonZero) :
    actualMaximumPredecessor a 0 = 0 := by
  have hm := actualMaximumPredecessor_correct a hpos ha 0
  exact actual_norm_zero _ (hm.1.1.trans ha) (Nat.eq_zero_of_le_zero hm.1.2)

theorem actualOptimizedMaximumBaseCases : Targets.ActualOptimizedMaximumBaseCases := by
  refine ⟨actual_maximum_zero_budget, ?_, ?_⟩
  · intro b
    have hone : (1 : Ordinal) < epsilonZero := by
      simpa only [ONote.repr_ofNat, Nat.cast_one] using
        rawNotation_repr_lt_epsilonZero (ONote.ofNat 1)
    have hm := actualMaximumPredecessor_correct 1 zero_lt_one hone b
    change actualMaximumPredecessor (Ordinal.omega0 ^ (0 : Ordinal)) b = 0
    rw [Ordinal.opow_zero]
    exact Order.lt_one_iff.mp hm.1.1
  · intro e he
    exact actual_maximum_zero_budget _ (Ordinal.opow_pos e Ordinal.omega0_pos)
      ((Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he)

theorem optimizedMaximumCallsDecrease : Targets.OptimizedMaximumCallsDecrease := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b charge hpos hle
    have hlt : b - charge < b := Nat.sub_lt (by omega) hpos
    unfold optimizedMaximumRank
    omega
  · intro b d w
    have hs := Nat.sub_le b (d * w)
    unfold optimizedMaximumRank
    omega
  · intro b hb
    unfold optimizedMaximumRank
    omega
  · intro e hpos he b hb
    dsimp only
    have hn := (actualMaximumPredecessor_correct e hpos he (b - 1)).1.2
    have hv : 1 + actualOrdinalNorm (actualMaximumPredecessor e (b - 1)) ≤ b := by omega
    have hp : 0 < 1 + actualOrdinalNorm (actualMaximumPredecessor e (b - 1)) := by omega
    refine ⟨hv, Nat.div_pos hv hp, ?_⟩
    have hm := Nat.mod_lt b hp
    unfold optimizedMaximumRank
    omega

end LogicLineages.OrdinalComparison
