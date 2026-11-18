module
public import LogicLineages.OrdinalComparison.EncodedFiniteBallsTargets
public import LogicLineages.OrdinalComparison.RawNormCodeTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullNormBalls.Targets
open LogicLineages.OrdinalComparison

def ActualNormComputation : Prop :=
  Nat.Primrec rawNormCode ∧
    ∀ a : NONote, rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr

/-- Actual semantic balls and complete effective hereditary-CNF interfaces. -/
def CompleteNormBalls : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualFiniteNormBalls ∧
  LogicLineages.OrdinalComparison.Targets.EncodedActualNormBallImage ∧
  LogicLineages.OrdinalComparison.Targets.EncodedNormalNormBallCorrect ∧
  LogicLineages.OrdinalComparison.Targets.EncodedNormalNormBallPrimitiveRecursive ∧
  LogicLineages.OrdinalComparison.Targets.RawNoteDecodeEncode ∧
  LogicLineages.OrdinalComparison.Targets.RawNoteEncodeDecode ∧
  LogicLineages.OrdinalComparison.Targets.RawComparisonOrdinalCorrect ∧
  LogicLineages.OrdinalComparison.Targets.RawComparisonPrimitiveRecursive ∧
  ActualNormComputation
end LogicLineages.CartierObserverCurrent.FullNormBalls.Targets
