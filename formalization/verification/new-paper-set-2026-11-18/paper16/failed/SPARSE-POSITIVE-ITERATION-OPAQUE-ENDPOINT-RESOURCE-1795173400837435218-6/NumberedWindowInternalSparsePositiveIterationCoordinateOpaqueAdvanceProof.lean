module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueAdvanceProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraph (programGraph)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof

attribute [local irreducible] Stable programGraph advance

/-- Type-level identity of the actual Program6 AST, not an equality of
external evaluation functions or of object-language predicates. -/
def advanceInputs : Fin 4 → Program 6 :=
  ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]

theorem advanceIdentity (r : Program 5) (l : Program 3) :
    advanceAtCell r l = .composition (advance r l) advanceInputs := rfl

private theorem inputStable (i : Fin 4) : Stable (advanceInputs i) :=
  Fin.cases context (Fin.cases ty (Fin.cases current
    (Fin.cases (readCell cellHead) (fun u => Fin.elim0 u)))) i

theorem advanceStable (r : Program 5) (l : Program 3) : Stable (advanceAtCell r l) := by
  rw [advanceIdentity]
  exact stableCompose (advance r l) advanceInputs inputStable

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueAdvanceProof
