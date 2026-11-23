module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinement
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (literal chooseBranch bothOne compareNumbers)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood field)
open NumberedWindowInternalAtomicRefinement (atSource atTarget bottomTarget)
open NumberedWindowInternalAuxBottomRefinement
  (auxShell auxFunction resultFits sourceFlag refineAuxBottom)

/-- Inspect the actual least representative carried by the original address.
Keep the auxiliary domain and the stored whole function type separate. -/
def auxDom : Program 1 := applyUnary (field 0) rawLeast
def auxFnType : Program 1 := applyUnary (field 0) auxFunction
def auxHeadFree : Program 1 := applyUnary (nodeGood (literal 1 0) 2) auxFunction
def freeAux : Program 1 := bothOne addressGood (bothOne auxShell (bothOne auxHeadFree resultFits))

def sameField (p : Program 1) : Program 3 := .composition compareNumbers ![atSource p,atTarget p]

/-- The original positive tape may change the least representative of the
raw right argument. The real context and every relevant type stay fixed. -/
def bottomAuxTarget : Program 3 :=
  bothOne (atTarget sourceFlag)
    (bothOne (sameField rawContext) (bothOne (sameField rawResult)
      (bothOne (sameField auxDom) (sameField auxFnType))))

/-- Only the whole-bottom branch obtains its scalar call here. An auxiliary
can have a different selected right argument; a scalar call on it is not
identified with the admitted raw intermediate of the original positive path. -/
def freeAuxTarget (i : Program 1) : Program 3 :=
  chooseBranch bottomTarget bottomAuxTarget (bothOne bottomTarget (atTarget i))

/-- Candidate physical refinement: the original r is tested on unchanged
inputs. The pre-existing bottom-auxiliary refinement is used verbatim.
Original numeric equality needs a separate proof. -/
def neutralPositive (i : Program 1) (r : Program 3) : Program 3 :=
  chooseBranch (atSource freeAux) (refineAuxBottom i r) (bothOne r (freeAuxTarget i))

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinement
