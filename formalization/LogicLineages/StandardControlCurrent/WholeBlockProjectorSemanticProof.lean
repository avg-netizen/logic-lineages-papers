module
public import LogicLineages.StandardControlCurrent.WholeBlockProjectorTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitHFreeOutputProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.WholeBlockProjectorProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion

theorem semantics : WholeBlockProjectorTargets.Semantics :=
  ⟨PlainBlockSplitProof.literalTieSemantics,
    PlainBlockSplitProof.strictOriginalBoundDecrease,
    PlainBlockSplitProof.actualOneStepProjection,
    PlainBlockSplitProof.wholeBlockStateClosure,
    PlainBlockSplitProof.originalBranchNameSupport,
    PlainBlockSplitProof.hFreeBranchClosure,
    PlainBlockSplitProof.actualUniformBlockProjection,
    PlainBlockSplitProof.originalOutputNameSupport,
    PlainBlockSplitProof.hFreeOutputClosure⟩
end LogicLineages.StandardControlCurrent.WholeBlockProjectorProof
