module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueUpdateProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueBranchProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraph (programGraph)
open InternalAcceptance (branch)
open NumberedWindowInternalSparseFieldCell (cellGood)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof
open NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueUpdateProof

attribute [local irreducible] Stable programGraph updateCell dead

def validOrDead (r : Program 5) (l : Program 3) : Program 6 :=
  branch (onCursor cellGood) dead (updateCell r l)

theorem stepIdentity (r : Program 5) (l : Program 3) :
    iterateStep r l = branch scratchCursor (.projection 1) (validOrDead r l) := rfl

private theorem innerStable (r : Program 5) (l : Program 3) :
    Stable (validOrDead r l) := by
  unfold validOrDead
  exact choice (onCursor cellGood) dead (updateCell r l) (readCell cellGood)
    deadStable (updateStable r l)

theorem stepStable (r : Program 5) (l : Program 3) : Stable (iterateStep r l) := by
  rw [stepIdentity]
  exact choice scratchCursor (.projection 1) (validOrDead r l) cursor prior (innerStable r l)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueBranchProof
