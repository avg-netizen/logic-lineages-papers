module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRaw
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open NumberedWindowInternalSparseRawRun (ownRun)

/-- All component inputs are selected from the unchanged source tape
[packed lexical context, result type, source, witness, destination]. -/
def sourceSyntax (syntaxProg : Program 1) : Program 5 :=
  .composition syntaxProg (fun _ : Fin 1 => .projection 2)

def destinationSyntax (syntaxProg : Program 1) : Program 5 :=
  .composition syntaxProg (fun _ : Fin 1 => .projection 4)

/-- This is the actual existing sparse own-witness loop, not a separately
compiled extensional raw checker. The unchanged witness occupies its
actual middle slot; ownRun uses that same witness as its fuel. -/
def ownCheck (root other : Program 3) : Program 5 :=
  .composition (ownRun root other) ![.projection 2,.projection 3,.projection 4]

def sourceWindow (windowProg : Program 3) : Program 5 :=
  .composition windowProg ![.projection 0,.projection 1,.projection 2]

def destinationWindow (windowProg : Program 3) : Program 5 :=
  .composition windowProg ![.projection 0,.projection 1,.projection 4]

/-- Keep both independent raw syntax guards, the literal underlying
own-run, and both original finite-context endpoint window guards. -/
def typedRaw5 (root other windowProg : Program 3) (syntaxProg : Program 1) : Program 5 :=
  conjunction
    (conjunction (conjunction (sourceSyntax syntaxProg) (destinationSyntax syntaxProg))
      (ownCheck root other))
    (conjunction (sourceWindow windowProg) (destinationWindow windowProg))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRaw
