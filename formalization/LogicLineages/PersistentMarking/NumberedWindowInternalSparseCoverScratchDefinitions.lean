module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratch
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalAcceptance (branch constantZero)
open InternalEqualityTest (predecessor)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowScalarAlgorithm (Settings)

/-- Retain the actual Option code. The same C is called on the original
fixed encoded head list, original fixed encoded type list, and original seed. -/
def coverOption (C : Program 3) (s : Settings) : Program 1 :=
  .composition C ![literal 1 (Encodable.encode s.window.2),
    literal 1 (Encodable.encode s.types),.projection 0]

/-- The only collapse occurs at this scratch boundary: none maps to nil,
and an actual some removes exactly the outer Option successor tag. -/
def optionPayload : Program 1 :=
  branch (.projection 0) (constantZero 1) predecessor

def scratchVertices (C : Program 3) (s : Settings) : Program 1 :=
  .composition optionPayload (fun _ : Fin 1 => coverOption C s)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratch
