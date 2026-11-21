module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings vertices edge)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState packedLeast)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdge (edge4 packedEdge)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseScalarEdgeNumericProof (calibration)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePackedLeast
open NumberedWindowInternalSparsePackedLeastTargets
open NumberedWindowInternalSparsePackedLeastNumericMinimumProof (allInput)
open NumberedWindowInternalSparsePackedLeastNumericTapeProof (contextValue membersValue)

private theorem edgeFiber (s : Settings) (X : Program 2) (W : Program 3)
    (hX : ActualTermExchange s X) (hW : ActualPackedWindow s W)
    (ctx ty : Nat) (g : List Nat) (parsed : unpack ctx = some g) :
    exactEdgeBit (edge4 X W) ctx ty = edge s g ty := by
  funext w v
  unfold exactEdgeBit
  rw [calibration s X W hX hW ctx ty w v]
  have bit : packedEdge s ctx ty w v = edge s g ty w v := by
    rw [packedEdge, parsed] <;> rfl
  rw [bit]
  cases edge s g ty w v <;> rfl

private theorem minimumValue (s : Settings) (C : Program 3) (X : Program 2) (W : Program 3)
    (hC : ActualSelectedCoverOutput C) (ctx ty seed : Nat) :
    evaluate (minimumAtMembers C X W s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      encodeState ((NumberedWindowClassAlgorithm.members (exactEdgeBit (edge4 X W) ctx ty)
        (vertices s seed) seed).min?) := by
  rw [minimumAtMembers, unaryValue, membersValue C X W hC s ctx ty seed, allInput, numbersRoundTrip] <;> rfl

theorem composition : ExactPackedLeastComposition := by
  intro s C X W hC hX hW ctx ty seed
  unfold packedLeast
  rw [packedLeastProgram, evalBranch, contextValue]
  cases parsed : unpack ctx with
  | none => rfl
  | some g =>
    change (if numbersNumber g + 1 = 0 then 0 else
      evaluate (minimumAtMembers C X W s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil)) =
      encodeState (NumberedWindowScalarAlgorithm.least s g ty seed)
    rw [if_neg (Nat.succ_ne_zero (numbersNumber g)), minimumValue s C X W hC ctx ty seed,
      edgeFiber s X W hX hW ctx ty g parsed] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericProof
