module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMap
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRawListRecursion InternalListCodec

def mapHead {k : Nat} (transform : Program (k + 1)) : Program (k + 2) :=
  .composition transform (Fin.cons (.projection 0) (fun i => .projection i.succ.succ))

def mapStep {k : Nat} (transform : Program (k + 1)) : Program (k + 2) :=
  .composition consCode (Fin.cons (mapHead transform) (Fin.cons (.projection 1) Fin.elim0))

/-- Map a concrete original PR program over the unchanged raw list code. -/
def map {k : Nat} (transform : Program (k + 1)) : Program (k + 1) :=
  listRec zero (mapStep transform)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMap
