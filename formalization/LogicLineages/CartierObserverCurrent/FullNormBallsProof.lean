module
public import LogicLineages.CartierObserverCurrent.FullNormBallsTargets
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullNormBalls
open LogicLineages.OrdinalComparison

theorem actualNormComputation : Targets.ActualNormComputation := by
  refine ⟨rawNormCodePrimitiveRecursive, ?_⟩
  intro a
  rw [rawNormCodeCorrect]
  exact (actualOrdinalNorm_notationCorrespondence a).symm

theorem completeNormBalls : Targets.CompleteNormBalls :=
  ⟨actualFiniteNormBalls, encodedActualNormBallImage, encodedNormalNormBallCorrect,
    encodedNormalNormBallPrimitiveRecursive, rawNoteDecodeEncode, rawNoteEncodeDecode,
    rawComparisonOrdinalCorrect, rawComparisonPrimitiveRecursive, actualNormComputation⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullNormBalls
end LogicLineages.CartierObserverCurrent.FullNormBalls
