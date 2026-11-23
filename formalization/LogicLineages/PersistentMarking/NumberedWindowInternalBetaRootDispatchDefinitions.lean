module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatch

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (branch)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)

def witnessTest : Program 3 := onRaw (nodeGood (literal 1 6) 0) 1

def betaCall (beta : Program 2) : Program 3 :=
  .composition beta ![.projection 0,.projection 2]

/-- Only the genuine arity-zero tag-6 root witness selects the beta leaf.
All other root witnesses are delegated to the same originally chosen AST. -/
def root' (original : Program 3) (beta : Program 2) : Program 3 :=
  branch witnessTest original (betaCall beta)

end LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatch
