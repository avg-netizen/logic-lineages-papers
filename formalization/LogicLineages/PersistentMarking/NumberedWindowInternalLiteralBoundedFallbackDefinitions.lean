module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallback
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalLessThan (ltTest)
open NumberedWindowInternalSparsePathEnvelope (applyUnary exactBody)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)

/-- The candidate uses the original optional-frame code: predecessor of
a positive candidate is the ordered [source,witness,target] scratch. -/
def childSelector : Program 1 := applyUnary cellHead (applyUnary cellTail predOne)
def frameShape : Program 1 := applyUnary (exactBody 3) predOne

def atCandidate (p : Program 1) : Program 2 := .composition p ![.projection 0]
def descends : Program 2 := .composition ltTest ![atCandidate childSelector,.projection 1]
def admitted : Program 2 := conjunction (atCandidate frameShape) descends

/-- Exact same candidate value, but only when its ordered code and
strictly decreasing witness are accepted by the physical guards. -/
def clip : Program 2 := branch admitted (constantZero 2) (.projection 0)
def fallback (other : Program 3) : Program 3 := .composition clip ![other,.projection 1]

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallback
