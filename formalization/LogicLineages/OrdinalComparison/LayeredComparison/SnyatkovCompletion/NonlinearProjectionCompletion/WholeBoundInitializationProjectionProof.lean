module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationClassProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
open WholeBoundInitialization

theorem actualInitializedProjection : WholeBoundInitializationTargets.ActualInitializedProjection := by
  intro bound p hnd hz ν
  exact (PlainBlockSplitProof.actualUniformBlockProjection bound («initialize» bound p) hnd
    (actualAllowedTest bound p hz) (wholeBoundParameterIndependence bound p) ν).trans
    (exactPrefixSemantics bound p ν)

theorem originalProjectedNameSupport : WholeBoundInitializationTargets.OriginalProjectedNameSupport := by
  intro bound p hnd hz j hj
  have h := PlainBlockSplitProof.originalOutputNameSupport bound («initialize» bound p) hnd
    (actualAllowedTest bound p hz) (wholeBoundParameterIndependence bound p) j hj
  exact ⟨h.1, (exactOriginalNameSupport bound p j).mp h.2⟩

theorem hFreeProjectedOutput : WholeBoundInitializationTargets.HFreeProjectedOutput := by
  intro bound p hnd hz
  exact PlainBlockSplitProof.hFreeOutputClosure bound («initialize» bound p) hnd
    (actualAllowedTest bound p hz) (wholeBoundParameterIndependence bound p)
    (hFreeInitialization bound p hz)

#print axioms actualInitializedProjection
#print axioms originalProjectedNameSupport
#print axioms hFreeProjectedOutput
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationProof
