module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueAdvanceProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueUpdateProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraph (programGraph)
open InternalAcceptance (constantZero)
open InternalListCodec (consCode)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof
open NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueAdvanceProof (advanceStable)

attribute [local irreducible] Stable programGraph advanceAtCell

theorem updateIdentity (r : Program 5) (l : Program 3) :
    updateCell r l = .composition consCode ![onCursor cellTail,advanceAtCell r l] := rfl

theorem deadIdentity : dead = .composition consCode ![constantZero 6,constantZero 6] := rfl

theorem updateStable (r : Program 5) (l : Program 3) : Stable (updateCell r l) := by
  rw [updateIdentity]
  exact binary consCode (onCursor cellTail) (advanceAtCell r l)
    (readCell cellTail) (advanceStable r l)

theorem deadStable : Stable dead := by
  rw [deadIdentity]
  exact binary consCode (constantZero 6) (constantZero 6) zero zero

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueUpdateProof
