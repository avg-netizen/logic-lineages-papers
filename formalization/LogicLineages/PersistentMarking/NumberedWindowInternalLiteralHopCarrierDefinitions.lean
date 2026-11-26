module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrier
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
  (branch conjunction)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan (constantOne)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)

def atSlot (p : Program 1) (i : Fin 5) : Program 5 := .composition p ![.projection i]

def addressGuards (cv tv : Program 1) : Program 5 := conjunction (atSlot cv 0) (atSlot tv 1)

def targetLeast (L : Program 3) : Program 5 := .composition L ![.projection 0,.projection 1,.projection 4]

def targetCode (L : Program 3) : Program 5 := .composition predOne ![targetLeast L]

def targetAddress (L : Program 3) : Program 5 :=
  .composition addressEmitter ![.projection 0,.projection 1,targetCode L]

def targetScalar (i : Program 1) (L : Program 3) : Program 5 := .composition i ![targetAddress L]

/-- The observation is activated only on the actual validated fiber
and a genuinely successful least. Raw checking elsewhere stays exactly
unchanged, even if it has no class address yet. -/
def targetGate (i cv tv : Program 1) (L : Program 3) : Program 5 :=
  branch (addressGuards cv tv) (constantOne 5)
    (branch (targetLeast L) (constantOne 5) (targetScalar i L))

def rawWithTarget (i cv tv : Program 1) (raw : Program 5) (L : Program 3) : Program 5 :=
  conjunction raw (targetGate i cv tv L)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrier
