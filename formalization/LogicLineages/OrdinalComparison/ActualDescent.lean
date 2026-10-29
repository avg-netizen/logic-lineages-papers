module
public import LogicLineages.OrdinalComparison.ActualDescentTargets
public import LogicLineages.OrdinalComparison.ActualSinglePredecessor

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem actual_tail_norm (a : Ordinal) (ha : a < epsilonZero) (n : Nat) :
    actualOrdinalNorm (a + (n : Ordinal)) = actualOrdinalNorm a + n := by
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  have ht := (finiteTailCorrect r n).1
  rw [hr] at ht
  rw [← ht, actualOrdinalNorm_notationCorrespondence (finiteTail r n),
    (finiteTailCorrect r n).2, ← actualOrdinalNorm_notationCorrespondence r, hr]

theorem actualNonfiniteDecomposition : Targets.ActualNonfiniteDecomposition := by
  intro a hnon ha
  have hle : actualLimitPart a ≤ a := Ordinal.mul_div_le a Ordinal.omega0
  have hlim : Order.IsSuccLimit (actualLimitPart a) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      ((Ordinal.div_pos Ordinal.omega0_ne_zero).mpr hnon)
  have ht : (actualTailPart a : Ordinal) = a % Ordinal.omega0 := by
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt a Ordinal.omega0_ne_zero)
    simp only [actualTailPart, hn, Ordinal.card_nat, Cardinal.toNat_natCast]
  have heq : a = actualLimitPart a + (actualTailPart a : Ordinal) := by
    rw [ht]
    exact (Ordinal.div_add_mod a Ordinal.omega0).symm
  refine ⟨hle.trans_lt ha, hlim, heq, ?_⟩
  calc
    actualOrdinalNorm a = actualOrdinalNorm (actualLimitPart a + (actualTailPart a : Ordinal)) :=
      congrArg actualOrdinalNorm heq
    _ = actualOrdinalNorm (actualLimitPart a) + actualTailPart a :=
      actual_tail_norm _ (hle.trans_lt ha) _

theorem actualDescentStepStrict : Targets.ActualDescentStepStrict := by
  intro a hnon ha
  have hd := actualNonfiniteDecomposition a hnon ha
  have hm := actualMaximumPredecessor_correct (actualLimitPart a) hd.2.1.bot_lt hd.1
    (Phi (actualOrdinalNorm a))
  exact hm.1.1.trans_le (Ordinal.mul_div_le a Ordinal.omega0)

theorem actualDescentStepCollapse : Targets.ActualDescentStepCollapse := by
  intro a hnon ha
  have hd := actualNonfiniteDecomposition a hnon ha
  have hr := actualSinglePredecessorRecurrence (actualLimitPart a) hd.1 hd.2.1 (actualTailPart a)
  rw [← hd.2.2.1, ← hd.2.2.2] at hr
  exact hr

theorem actualDescentStepNorm : Targets.ActualDescentStepNorm := by
  intro a hnon ha
  have hd := actualNonfiniteDecomposition a hnon ha
  exact actualLimitMaximumPredecessorSaturation (actualLimitPart a) hd.1 hd.2.1
    (Phi (actualOrdinalNorm a))

end LogicLineages.OrdinalComparison
