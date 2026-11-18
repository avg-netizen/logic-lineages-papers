module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.WholeBlockProjectorTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion

/-- All actual semantic dispatcher, state, progress, projection and closure obligations. -/
def Semantics : Prop :=
  PlainBlockSplitTargets.LiteralTieSemantics ∧
  PlainBlockSplitTargets.StrictOriginalBoundDecrease ∧
  PlainBlockSplitTargets.ActualOneStepProjection ∧
  PlainBlockSplitTargets.WholeBlockStateClosure ∧
  PlainBlockSplitTargets.OriginalBranchNameSupport ∧
  PlainBlockSplitTargets.HFreeBranchClosure ∧
  PlainBlockSplitTargets.ActualUniformBlockProjection ∧
  PlainBlockSplitTargets.OriginalOutputNameSupport ∧
  PlainBlockSplitTargets.HFreeOutputClosure

/-- Literal ordered branch lists and actual finite iteration on arbitrary raw states. -/
def Dispatch : Prop :=
  PlainBlockDispatchCodeTargets.LiteralRenameCalibration ∧
  PlainBlockDispatchCodeTargets.LiteralBranchFamiliesCalibration ∧
  PlainBlockDispatchCodeTargets.LiteralBranchAssemblyCalibration ∧
  PlainBlockDispatchCodeTargets.LiteralAdvanceCalibration ∧
  PlainBlockDispatchCodeTargets.LiteralRunCalibration ∧
  PlainBlockDispatchCodeTargets.ActualDispatchPrograms

/-- Actual readout and bounded projector, with both typed exactness and joint raw computation. -/
def Projection : Prop :=
  PlainBlockProjectionCodeTargets.LiteralTermCalibration ∧
  PlainBlockProjectionCodeTargets.LiteralAtomCalibration ∧
  PlainBlockProjectionCodeTargets.LiteralFormulaCompilation ∧
  PlainBlockProjectionCodeTargets.LiteralReadoutCalibration ∧
  PlainBlockProjectionCodeTargets.LiteralProjectorCalibration ∧
  PlainBlockProjectionCodeTargets.ActualProjectionPrograms

def Initialized : Prop :=
  WholeBoundProjectionCodeTargets.LiteralInitializedProjection ∧
  WholeBoundProjectionCodeTargets.ActualJointProgram

def Full : Prop := Semantics ∧ Dispatch ∧ Projection ∧ Initialized
end LogicLineages.StandardControlCurrent.WholeBlockProjectorTargets
