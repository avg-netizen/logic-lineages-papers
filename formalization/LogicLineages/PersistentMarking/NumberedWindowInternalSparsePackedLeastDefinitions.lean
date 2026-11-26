module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeast
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalAcceptance (branch constantZero)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)

/-- Test the actual original sparse parser Option on slot 0. A valid
empty context has a successor tag; do not test its nil scratch payload. -/
def contextOption : Program 3 :=
  .composition parser (fun _ : Fin 1 => .projection 0)

/-- The actual same cover C on the original seed at slot 2. -/
def poolAtSeed (C : Program 3) (s : Settings) : Program 3 :=
  .composition (scratchVertices C s) (fun _ : Fin 1 => .projection 2)

/-- Original supplied vertices, original packed ctx, requested type, and
seed, on the same physical length-fuel member calculation with edge4 X W. -/
def membersAtSeed (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Program 3 :=
  .composition (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]

def minimumAtMembers (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Program 3 :=
  .composition scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)

/-- The original packed least interface, on [ctx,ty,seed]. The parser
only selects its actual Option branch; the same unchanged packed ctx
is still passed to the same physical endpoint-guarded directed edge. -/
def packedLeastProgram (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Program 3 :=
  branch contextOption (constantZero 3) (minimumAtMembers C X W s)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeast
