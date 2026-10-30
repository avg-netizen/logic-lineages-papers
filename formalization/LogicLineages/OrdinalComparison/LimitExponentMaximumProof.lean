module
public import LogicLineages.OrdinalComparison.LimitExponentMaximumTargets
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public import LogicLineages.OrdinalComparison.ActualTailSeparation

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLimitExponentMaximum : Targets.ActualLimitExponentMaximum := by
  intro beta hl he budget hb
  dsimp only
  let delta := actualMaximumPredecessor beta (budget-1)
  have hd := actualMaximumPredecessor_correct beta hl.bot_lt he (budget-1)
  have hde : delta < epsilonZero := hd.1.1.trans he
  have hn : actualOrdinalNorm delta=budget-1 :=
    actualLimitMaximumPredecessorSaturation beta he hl (budget-1)
  have hpow : Ordinal.omega0^beta < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr he
  have hrec := actualLowerPowerGreedyRecurrence beta hl.bot_lt he budget hb
  dsimp only at hrec
  change actualLowerPowerMaximum beta budget = Ordinal.omega0^delta *
    ((budget/(1+actualOrdinalNorm delta) : Nat) : Ordinal) +
      actualLowerPowerMaximum delta (budget%(1+actualOrdinalNorm delta)) at hrec
  rw [hn, show 1+(budget-1)=budget by omega, Nat.div_self hb, Nat.mod_self,
    actualOptimizedMaximumBaseCases.2.2 delta hde, Nat.cast_one, mul_one, add_zero] at hrec
  have hM : actualMaximumPredecessor (Ordinal.omega0^beta) budget=Ordinal.omega0^delta := hrec
  have hN : actualOrdinalNorm (Ordinal.omega0^delta)=budget := by
    rw [← hM]
    exact actualLimitMaximumPredecessorSaturation _ hpow
      (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hl.bot_lt)) _
  refine ⟨hpow, hd.1.1, hn, hM, hN, ?_⟩
  intro htwo
  by_contra hh
  have hz : delta=0 := le_antisymm (not_lt.mp hh) zero_le
  have hzero : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  rw [hz, hzero] at hn
  omega

theorem actualLimitExponentBudgetStrict : Targets.ActualLimitExponentBudgetStrict := by
  intro beta hl he a b ha hab
  have hA := actualLimitExponentMaximum beta hl he a ha
  have hB := actualLimitExponentMaximum beta hl he b (ha.trans hab)
  have hle := actualMaximumJointMonotone beta beta hl.bot_lt le_rfl he (a-1) (b-1)
    (Nat.sub_le_sub_right hab.le 1)
  apply lt_of_le_of_ne hle
  intro heq
  have hna := hA.2.2.1
  have hnb := hB.2.2.1
  rw [heq] at hna
  omega

end LogicLineages.OrdinalComparison
