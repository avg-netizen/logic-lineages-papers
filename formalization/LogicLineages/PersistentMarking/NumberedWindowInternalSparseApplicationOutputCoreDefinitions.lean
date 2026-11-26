module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCore
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalEqualityTest (equalityTest predecessor)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)

/-- Actual arithmetic tape: packed context, domain, codomain, function
least code, argument least code, proposed output address. Emit just the
original raw tag6 application, not an address already claiming it least. -/
def seed : Program 6 :=
  consOf (literal 6 6)
    (consOf (.projection 1) (consOf (.projection 2) (consOf (.projection 3)
      (consOf (.projection 4) (constantZero 6)))))

/-- The identical physical least program is called at context and
codomain with precisely that raw application seed. -/
def selectedLeast (least : Program 3) : Program 6 :=
  .composition least ![.projection 0,.projection 2,seed]

def selectedClass (least : Program 3) : Program 6 :=
  .composition predecessor (fun _ : Fin 1 => selectedLeast least)

def outputAddress (least : Program 3) : Program 6 :=
  .composition addressEmitter ![.projection 0,.projection 2,selectedClass least]

def compareOutput (least : Program 3) : Program 6 :=
  .composition equalityTest ![.projection 5,outputAddress least]

/-- Zero optional least is rejected even if the raw comparison would
otherwise match a default address. Only a genuine positive optional
output is decoded to its predecessor for the original address emitter. -/
def outputCore (least : Program 3) : Program 6 :=
  branch (selectedLeast least) (constantZero 6) (compareOutput least)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCore
