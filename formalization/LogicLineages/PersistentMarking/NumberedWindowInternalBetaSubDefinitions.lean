module
public import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaSub

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (branch constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest (equalityTest)

def code (arg body : Nat) : Nat :=
  (((NumberedWindowSingletonAlgorithm.output arg 0 body).1).map Nat.succ).getD 0

def run2 (p : Program 2) (a b : Nat) : Nat := evaluate p (a ::ᵥ b ::ᵥ nil)

def Fits (sub : Program 2) : Prop := ∀ arg body, run2 sub arg body = code arg body

/-- The visible control keeps the original syntax and binder tests before
comparing the direct optional result with the successor of the target. -/
def betaChecker (guard arg body : Program 2) (sub : Program 2) : Program 2 :=
  branch guard (constantZero 2)
    (.composition equalityTest ![.composition sub ![arg,body],
      .composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))])

end LogicLineages.PersistentMarking.NumberedWindowInternalBetaSub
