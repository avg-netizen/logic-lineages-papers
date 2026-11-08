module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosure
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The concrete original state selectors must exhibit status ONE, empty
work and EXACTLY one result. A zero result is accepted; an empty result list
is not. This is an actual finite Program, not a semantic success predicate
or a field asserting that the recursive computation has been proved. -/
def goodState : Program 1 :=
  InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne InternalApplicationResultStack.status)
    (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch InternalApplicationResultStack.work
      (InternalAcceptance.branch InternalApplicationResultStack.results
        (InternalAcceptance.constantZero 1)
        (InternalAcceptance.branch
          (InternalApplicationResultStack.tailOf InternalApplicationResultStack.results)
          (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)))
      (InternalAcceptance.constantZero 1))

/-- Check the WHOLE final state of the unchanged run at its own exact
2*original-payload+1 count. Do not replace this graph internally by the
external fact that every natural input passes the check. -/
def goodRun (guard leaf : Program 1) (combine : Program 4) : Program 1 :=
  .composition goodState (fun _ : Fin 1 =>
    InternalApplicationResultStack.run guard leaf combine)

/-- The original singleton worklist [visit value], using the unchanged
original pair and raw-list constructors. This is the work in initial. -/
def visitWork : Program 1 :=
  consOf (InternalApplicationResultStack.visitOf (.projection 0))
    (InternalAcceptance.constantZero 1)

/-- Literal object-language 2*payload+1, written using addition and successor
so the bound is not supplied by a freely chosen count graph. -/
def payloadFuel {α : Type} (payload : OrdinaryArithmetic.Term α) :
    OrdinaryArithmetic.Term α :=
  OrdinaryArithmetic.succTerm (OrdinaryArithmetic.addTerm payload payload)

/-- BOTH actual program graphs are retained. The raw fold graph alone may
return its default zero and is never taken as evidence of successful shape.
The guard is explicit for later selected-edge/typed consumers; this formula
does not claim an unguarded internal totality or source accessibility proof. -/
def certifiedFold {α : Type} (guard leaf : Program 1) (combine : Program 4)
    (out value : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (goodRun guard leaf combine) InternalOriginalStepGuard.one value ⊓
    graph1 (InternalApplicationResultStack.fold guard leaf combine) out value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosure
