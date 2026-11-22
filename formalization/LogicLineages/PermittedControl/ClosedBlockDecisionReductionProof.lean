module
public import LogicLineages.PermittedControl.ClosedBlockDecisionTargets
import LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQueryStatementChecks
import LogicLineages.PermittedControl.StageCallbackSupplierStatementChecks

public section
namespace LogicLineages.PermittedControl.ClosedBlockDecision
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedRawStageQuery (result)
open OriginalPrintedRawSelectedStageQuery (ForControl)
open StageCallbackSupplier (stageChildren)

theorem exactClosedBlockFromEmitter : ExactClosedBlockFromEmitter := by
  intro f B control emitter
  obtain ⟨alt,shape,exact,high,computable,emits⟩ := emitter
  have stage := StatementChecks.fixed_exactSuppliedStageCallback f B alt shape exact high emits
  exact ⟨result f B high,control.2 high computable,control.1 high (stageChildren alt B) stage⟩

theorem exactClosedBlockReduction : ExactClosedBlockReduction := by
  intro factorial near
  have selected := StatementChecks.fixed_exactOriginalRawSelectedStageQuery
  exact ⟨exactClosedBlockFromEmitter _ _ selected.1 factorial,
    fun b => exactClosedBlockFromEmitter _ _ (selected.2 b) (near b)⟩

theorem fullClosedBlockDecisionReduction : FullClosedBlockDecisionReduction :=
  ⟨exactClosedBlockFromEmitter,exactClosedBlockReduction⟩

#print axioms exactClosedBlockFromEmitter
#print axioms exactClosedBlockReduction
#print axioms fullClosedBlockDecisionReduction
end LogicLineages.PermittedControl.ClosedBlockDecision
