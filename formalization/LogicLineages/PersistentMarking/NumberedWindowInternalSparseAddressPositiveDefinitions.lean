module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositive
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePositiveFold (positive)

/-- Literal outer certificate tape is [source address, raw certificate,
target address]. Source/destination extraction cannot move slot one. -/
def atAddress (p : Program 1) (slot : Fin 3) : Program 3 :=
  .composition p (fun _ : Fin 1 => .projection slot)

def sideGood (ctxValid tyValid : Program 1) (slot : Fin 3) : Program 3 :=
  conjunction (atAddress addressGood slot)
    (conjunction (atAddress (applyUnary ctxValid rawContext) slot)
      (atAddress (applyUnary tyValid rawResult) slot))

def sameField (p : Program 1) : Program 3 :=
  .composition equalityTest ![atAddress p 0, atAddress p 2]

def callFold (raw : Program 5) (least : Program 3) : Program 3 :=
  .composition (positive raw least)
    ![atAddress rawContext 0, atAddress rawResult 0, atAddress rawLeast 0,
      .projection 1, atAddress rawLeast 2]

/-- One new selected original numerical address checker. Its two
literal tag-three reports are validated, then same packed context and
literal type, then the unchanged same-fiber positive fold. There is no
new independent scalar-admission check. -/
def addressPositive (ctxValid tyValid : Program 1) (raw : Program 5) (least : Program 3) : Program 3 :=
  conjunction (sideGood ctxValid tyValid 0)
    (conjunction (sideGood ctxValid tyValid 2)
      (conjunction (sameField rawContext) (conjunction (sameField rawResult) (callFold raw least))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositive
