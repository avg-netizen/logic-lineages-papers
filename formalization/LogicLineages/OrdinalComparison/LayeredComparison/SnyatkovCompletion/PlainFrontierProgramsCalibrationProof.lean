module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDecisionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof
open NormalForm (Formula)
open PlainFrontierPrograms

private theorem step_first (p : Formula) :
    (PlainBranchSplitPrograms.Code.step p.encode).1 = (PlainBranchSplit.step p).1 :=
  congrArg Prod.fst (PlainBranchSplitProgramsProof.literalStep p)
private theorem step_second (p : Formula) :
    (PlainBranchSplitPrograms.Code.step p.encode).2 = (PlainBranchSplit.step p).2.map Formula.encode :=
  congrArg Prod.snd (PlainBranchSplitProgramsProof.literalStep p)

theorem literalAdvance : PlainFrontierProgramsTargets.LiteralAdvance := by
  intro s
  apply Prod.ext
  · simp only [Code.advance, encodeState, PlainFrontier.advance, List.any_map,
      Function.comp_def, step_first]
  · simp only [Code.advance, encodeState, PlainFrontier.advance, List.flatMap_map,
      List.map_flatMap, Function.comp_def, step_second]

theorem literalIteration : PlainFrontierProgramsTargets.LiteralIteration := by
  intro n s
  induction n with
  | zero => rfl
  | succ n ih =>
      have hc : Code.run (n + 1) (encodeState s) = Code.advance (Code.run n (encodeState s)) :=
        Function.iterate_succ_apply' Code.advance n (encodeState s)
      rw [hc, PlainFrontierProof.run_succ, ih, literalAdvance (PlainFrontier.run n s)]

theorem fuel_calibration (p : Formula) : Code.fuel p.encode = PlainFrontier.fuel p := by
  simp only [Code.fuel, PlainFrontier.fuel, MaximalPlainBranchProgramsProof.variables_calibration]

theorem initial_calibration (p : Formula) : Code.initial p.encode = encodeState (PlainFrontier.initial p) := rfl

theorem answer_calibration (p : Formula) : Code.answer p.encode = PlainFrontier.answer p := by
  unfold Code.answer PlainFrontier.answer
  rw [fuel_calibration, initial_calibration, literalIteration]
  rfl

theorem decide_calibration (p : Formula) : Code.decide p.encode = PlainFrontier.decide p := by
  unfold Code.decide PlainFrontier.decide
  rw [MaximalPlainBranchProgramsProof.isPlain_calibration, answer_calibration]

theorem literalDecisionData : PlainFrontierProgramsTargets.LiteralDecisionData :=
  fun p => ⟨fuel_calibration p, initial_calibration p, answer_calibration p, decide_calibration p⟩

theorem actualEncodedDecision : PlainFrontierProgramsTargets.ActualEncodedDecision := by
  intro p hp b
  rw [decide_calibration]
  exact PlainFrontierProof.exactRejectingDecision.2 p hp b

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof
