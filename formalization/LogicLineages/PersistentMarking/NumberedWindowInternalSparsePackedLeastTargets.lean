module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState ActualLeastCalibration)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePackedLeast

/-- Every standard scratch code for the actual original ordered minimum
recursor, including nil and the successful selected value zero. -/
def ExactAllInputScratchMinimum : Prop :=
  ∀ code : Nat,
    evaluate scratchMinimum (code ::ᵥ nil) =
      encodeState (((decodeNumbers code).getD []).min?)

/-- Compose actual named original callbacks on every raw packed input.
The result is the existing encoded sparse packed least API, not an
independent extensionally selected implementation or a valid-only guard. -/
def ExactPackedLeastComposition : Prop :=
  ∀ (s : Settings) (C : Program 3) (X : Program 2) (W : Program 3),
    ActualSelectedCoverOutput C → ActualTermExchange s X → ActualPackedWindow s W →
    ActualLeastCalibration s (packedLeastProgram C X W s)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
