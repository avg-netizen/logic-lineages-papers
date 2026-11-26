module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeBranchCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode

theorem literalAdvanceCalibration : PlainBlockDispatchCodeTargets.LiteralAdvanceCalibration := by
  intro states
  unfold advance PlainBlockSplit.advance
  rw [List.flatMap_map, List.map_flatMap]
  apply congrArg (fun f : PlainBlockSplit.State → List StateData => states.flatMap f)
  funext s
  dsimp only [Function.comp_def, stateData]
  by_cases h : s.1 = []
  · simp only [h, reduceIte, List.map_cons, List.map_nil, stateData]
  · simp only [h, reduceIte]
    exact literalBranchAssemblyCalibration s.1 s.2
#print axioms literalAdvanceCalibration

theorem literalRunCalibration : PlainBlockDispatchCodeTargets.LiteralRunCalibration := by
  intro fuel states
  induction fuel with
  | zero => rfl
  | succ n ih =>
      change advance^[n+1] (states.map stateData) = (PlainBlockSplit.advance^[n+1] states).map stateData
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change advance (run n (states.map stateData)) = (PlainBlockSplit.advance (PlainBlockSplit.run n states)).map stateData
      rw [ih]
      exact literalAdvanceCalibration (PlainBlockSplit.run n states)
#print axioms literalRunCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
