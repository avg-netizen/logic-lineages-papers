module

public import LogicLineages.ComputabilityKnowledge.PredictionFlipLearningTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFlipMaskProof
public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFlipLearningProof
open PredictionGame PredictionLearning PredictionFiniteChange PredictionCodeEvader PredictionFlipMask
open PredictionBaselineGame PredictionUniformHistory PredictionFlipLearningTargets

theorem actualFlipPolicyCalibration : ActualFlipPolicyCalibration := by
  intro R b z e n
  exact (PredictionSelfHistoryProof.actualHistoryCalibration (flipRule R b z) e n).2

theorem uniformFlipPolicyProgram : UniformFlipPolicyProgram := by
  intro R b hR hb
  obtain ⟨u, hu, _, hprog⟩ := PredictionUniformHistoryProof.uniformSelfHistoryProgram
    (flipRule R b) (PredictionFlipMaskProof.flipRuleComputable R b hR hb)
  exact ⟨u, hu, fun z => (hprog z).2⟩

theorem positiveFlipLearning : PositiveFlipLearning := by
  intro R b z hfin e he hav
  let p := flipPolicy R b z
  let q := policy e he
  obtain ⟨F, hF⟩ := PredictionFlipMaskProof.finiteActualFlipMask R z hfin p q
  obtain ⟨B, hB⟩ := PredictionComputableBudgetProof.actualAnyPredictorBaselineCorrect b p e he hav
  refine ⟨max F B, ?_⟩
  intro n hn
  have hFn : F ≤ n := (Nat.le_max_left _ _).trans hn
  have hBn : B ≤ n := (Nat.le_max_right _ _).trans hn
  have hcal := actualFlipPolicyCalibration R b z q n
  change prediction p q n = if flipEvent R z (histories p q n).evasions then
    !(budgetRule b (histories p q n).evasions (histories p q n).predictions)
    else budgetRule b (histories p q n).evasions (histories p q n).predictions at hcal
  rw [hF n hFn] at hcal
  simp only [Bool.false_eq_true, ↓reduceIte] at hcal
  exact hcal.trans (hB n hBn)

theorem negativeFlipLearning : NegativeFlipLearning := by
  intro R b z k hinf e he heq hav hlearn
  let p := flipPolicy R b z
  let q := policy e he
  obtain ⟨L, hL⟩ := hlearn
  obtain ⟨B, hB⟩ := PredictionComputableBudgetProof.actualAnyPredictorBaselineCorrect b p e he hav
  obtain ⟨n, hn, hflip⟩ := PredictionFlipMaskProof.infiniteCodeFlipMask R z k hinf p (max L B)
  rw [← heq] at hflip
  have hLn : L ≤ n := (Nat.le_max_left _ _).trans hn
  have hBn : B ≤ n := (Nat.le_max_right _ _).trans hn
  have hcal := actualFlipPolicyCalibration R b z q n
  change prediction p q n = if flipEvent R z (histories p q n).evasions then
    !(budgetRule b (histories p q n).evasions (histories p q n).predictions)
    else budgetRule b (histories p q n).evasions (histories p q n).predictions at hcal
  rw [hflip] at hcal
  simp only [↓reduceIte] at hcal
  rw [hB n hBn] at hcal
  have hwrong : Bool.not (evasion p q n) = evasion p q n := hcal.symm.trans (hL n hLn)
  cases hv : evasion p q n <;> simp [hv] at hwrong

end LogicLineages.ComputabilityKnowledge.PredictionFlipLearningProof
