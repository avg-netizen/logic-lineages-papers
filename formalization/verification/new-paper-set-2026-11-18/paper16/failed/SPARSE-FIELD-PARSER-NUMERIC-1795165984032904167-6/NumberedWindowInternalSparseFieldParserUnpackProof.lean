module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserLoopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserUnpackProof
open NumberedWindowInternalSparseFieldParserTargets
open NumberedWindowInternalSparseFieldParserLoopProof (terminalSteps enough)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair tailBound)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowFieldAlgorithm
open NumberedWindowPairAlgorithm (pair decode)
open LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof (numbersRoundTrip)

theorem scratch : ScratchBridge := by
  intro xs
  exact numbersRoundTrip xs

theorem bounded : BoundedOriginalFuelAccumulator := enough

theorem casesUnpack : OriginalUnpackCases := by
  refine ⟨rfl, ?_, ?_⟩
  · intro n h
    have missing : decode n = none := (allInput.2 n).symm.trans h
    unfold unpack
    rw [steps, step, missing]
    change finish (steps n none) = none
    rw [terminalSteps (s := none) trivial]
    rfl
  · intro h t
    unfold unpack
    rw [steps, step, encodedPair]
    change finish (steps (pair h t) (some (t,[h]))) = _
    simpa using enough t (pair h t) [h] (tailBound h t)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserUnpackProof
