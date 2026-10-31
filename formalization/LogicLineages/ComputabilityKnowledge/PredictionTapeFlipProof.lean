module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeFlipTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFlipMaskProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapePolicyCompilerProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeGameProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeFlipProof
open PredictionGame PredictionTapeObservation PredictionFiniteChange PredictionCodeEvader
open PredictionTapeGame PredictionTapeFlip PredictionTapeFlipTargets
open PredictionFlipMask (flipEvent)

private theorem actualFlipPolicyCalibration (R : Matrix) (b : Nat → Nat) (z : Nat) (e : Policy) (n : Nat) :
    let p := flipPolicy R b z
    let h := histories p e n
    prediction p e n = if flipEvent R z h.evasions then !(budgetRule b h.evasions h.predictions)
      else budgetRule b h.evasions h.predictions := by
  exact (PredictionSelfHistoryProof.actualHistoryCalibration (flipRule R b z) e n).2

theorem computableFlipRule : ComputableFlipRule := by
  intro R b hR hb
  have he : Computable (fun q : Nat × List Bool × List Bool => flipEvent R q.1 q.2.1) := by
    apply ((PredictionFlipMaskProof.flipEventComputable R hR).comp (Computable.fst.pair (Computable.fst.comp Computable.snd))).of_eq
    intro q
    dsimp only
  have hbase : Computable (fun q : Nat × List Bool × List Bool => budgetRule b q.2.1 q.2.2) :=
    Computable.comp (f := fun q : List Bool × List Bool => budgetRule b q.1 q.2)
      (g := fun q : Nat × List Bool × List Bool => q.2)
      (PredictionTapeGameProof.computableBudgetRule b hb) Computable.snd
  have hnot := (Primrec.dom_bool Bool.not).to_comp.comp hbase
  apply (Computable.cond he hnot hbase).of_eq
  intro q
  unfold flipRule
  cases flipEvent R q.1 q.2.1 <;> rfl

theorem uniformTapeFlipProgram : UniformTapeFlipProgram := by
  intro R b hR hb
  exact PredictionTapePolicyCompilerProof.uniformSelfHistoryTapeProgram (flipRule R b)
    (computableFlipRule R b hR hb)

theorem positiveTapeFlipLearning : PositiveTapeFlipLearning := by
  intro R b z hfin e he hav
  let p := flipPolicy R b z
  let q := policy e he
  obtain ⟨F, hF⟩ := PredictionFlipMaskProof.finiteActualFlipMask R z hfin p q
  obtain ⟨B, hB⟩ := PredictionTapeGameProof.actualAnyPredictorBaselineCorrect b p e he hav
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

theorem negativeTapeFlipLearning : NegativeTapeFlipLearning := by
  intro R b z k hinf e he heq hav hlearn
  let p := flipPolicy R b z
  let q := policy e he
  obtain ⟨L, hL⟩ := hlearn
  obtain ⟨B, hB⟩ := PredictionTapeGameProof.actualAnyPredictorBaselineCorrect b p e he hav
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

end LogicLineages.ComputabilityKnowledge.PredictionTapeFlipProof
