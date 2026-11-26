module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenChecks
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets
open NumberedWindowInternalSparseRawFunctionFrameOpenGuardProof (liftedTape literalTape)
open NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof (emit)

theorem exact_OpenLiteralFunctionFrame : ExactOpenLiteralFunctionFrame := by
  intro body α dom cod arg src child dst
  let xs := liftedTape dom cod arg src child dst
  have facts := literalTape (body := body) (Γ := []) dom cod arg src child dst
  exact successorBranchIntro frameGood (constantZero 3) emitFrame
    (frameValueTerm src child dst) z xs facts.guard (emit xs src child dst facts)

#print axioms exact_OpenLiteralFunctionFrame
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenChecks
