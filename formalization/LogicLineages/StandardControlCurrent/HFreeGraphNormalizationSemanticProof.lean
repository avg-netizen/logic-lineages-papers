module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphRealizationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphUniquenessProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphPlainProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphZeroShiftProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationClassProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationSemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization OriginalSourceElimination

theorem termGraphs : HFreeGraphNormalizationTargets.TermGraphs :=
  ⟨ExpandedGraphProof.literalSubtraction,ExpandedGraphProof.literalDivision,
   ExpandedGraphProof.literalInverse,ExpandedGraphProof.exactAllocation,
   ExpandedGraphProof.exactGraphSupport,ExpandedGraphProof.plainOriginalGraphClass,
   ExpandedGraphProof.graphSoundness,ExpandedGraphProof.totalGraphRealization,
   ExpandedGraphProof.allocatedNodeUniqueness⟩

theorem matrixGraphs : HFreeGraphNormalizationTargets.MatrixGraphs :=
  ⟨ExpandedBooleanGraphProof.literalForestSupport,ExpandedBooleanGraphProof.hFreeOriginalForest,
   ExpandedBooleanGraphProof.actualPredicateInterpretation,ExpandedBooleanGraphProof.exactFreshGraphNames,
   ExpandedBooleanGraphProof.originalGraphNameSupport,ExpandedBooleanGraphProof.literalZeroShiftGraphClass,
   ExpandedBooleanGraphProof.actualExpandedMatrixGraph⟩

theorem allowedWholeBlock : HFreeGraphNormalizationTargets.AllowedWholeBlock := by
  intro i p hp
  have hf := ExpandedBooleanGraphProof.exactFreshGraphNames [i] p
  have hn : (binderBlock i p).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hf.1⟩
    intro hi
    exact (hf.2 i hi).1 (List.mem_singleton_self i)
  have hc : WholeBoundInitialization.ZeroShift (graphFormula i p) :=
    ExpandedBooleanGraphProof.literalZeroShiftGraphClass [i] p hp
  refine ⟨hn,WholeBoundInitializationProof.actualAllowedTest _ _ hc,
    WholeBoundInitializationProof.wholeBoundParameterIndependence _ _,
    WholeBoundInitializationProof.hFreeInitialization _ _ hc,?_⟩
  intro ν
  have h := WholeBoundInitializationProof.exactPrefixSemantics (binderBlock i p) (graphFormula i p) ν
  change (PlainBlockSplit.existsPrefix ν (binderBlock i p) (normalized i p) ↔
    ∃ n : Nat, NormalForm.existsPrefix (Function.update ν i n) (graphNames i p) (graphFormula i p)) at h
  exact h.trans (exists_congr fun n =>
    ExpandedBooleanGraphProof.actualExpandedMatrixGraph [i] p (Function.update ν i n) hp)

theorem originalSupport : HFreeGraphNormalizationTargets.OriginalSupport := by
  intro i p hp
  refine ⟨?_,?_⟩
  · intro j hj
    have h := (ExpandedBooleanGraphProof.exactFreshGraphNames [i] p).2 j hj
    exact ⟨fun he => h.1 (List.mem_singleton.mpr he),h.2⟩
  · intro j hj
    have h := (WholeBoundInitializationProof.exactOriginalNameSupport
      (binderBlock i p) (graphFormula i p) j).mp hj
    exact ExpandedBooleanGraphProof.originalGraphNameSupport [i] p j h
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
