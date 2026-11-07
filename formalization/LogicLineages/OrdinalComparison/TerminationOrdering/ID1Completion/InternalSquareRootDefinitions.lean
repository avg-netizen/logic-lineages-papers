module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRoot
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Both step inputs are literal source inputs [counter, previous root]. -/
def successorCounter : Program 2 := .composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2))
def successorRoot : Program 2 := .composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))
def nextSquare : Program 2 := .composition InternalArithmeticPrograms.multiplication
  (Fin.cons successorRoot (Fin.cons successorRoot Fin.elim0))
def belowNextSquare : Program 2 := .composition InternalLessThan.ltTest
  (Fin.cons successorCounter (Fin.cons nextSquare Fin.elim0))
/-- A zero comparator result crosses the next square; a one result retains
exactly the previous root. The conditional and recursion are original ASTs. -/
def step : Program 2 := InternalAcceptance.branch belowNextSquare successorRoot (.projection (1 : Fin 2))
def root : Program 1 := .recursion .zero step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRoot
