module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinement
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (literal compareNumbers chooseBranch bothOne)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood field)
open NumberedWindowInternalAtomicRefinement (atSource atTarget bottomTarget)

/-- Two literal physical fields of the original raw auxiliary payload. -/
def auxCodomain : Program 1 := applyUnary (field 1) rawLeast
def auxFunction : Program 1 := applyUnary (field 2) rawLeast

def auxShell : Program 1 := applyUnary (nodeGood (literal 1 6) 4) rawLeast
def auxHeadBottom : Program 1 := applyUnary (nodeGood (literal 1 3) 1) auxFunction

def resultFits : Program 1 :=
  .composition compareNumbers (Fin.cons rawResult (Fin.cons auxCodomain Fin.elim0))

/-- Actual address tag3, actual raw application tag6/exact4, bare
bottom in its function slot, and the same reported/raw codomain.
This is structural recognition, not a lexical or window test. -/
def sourceFlag : Program 1 :=
  bothOne addressGood (bothOne auxShell (bothOne auxHeadBottom resultFits))

/-- Same source/certificate/result tape as the original positive
checker. Do not read, replace, or synthesize the supplied certificate. -/
def acceptedTerminal (i : Program 1) (r : Program 3) : Program 3 :=
  bothOne r (bothOne bottomTarget (atTarget i))

/-- Outside the strict bottom-headed auxiliary shape, retain old r
unchanged. The selected terminal arm is paid by actual old positive
success, actual terminal result and actual scalar(y). -/
def refineAuxBottom (i : Program 1) (r : Program 3) : Program 3 :=
  chooseBranch (atSource sourceFlag) r (acceptedTerminal i r)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinement
