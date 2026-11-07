module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticPrograms
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Increment the previous result, ignoring counter and fixed parameter. -/
def additionStep : Program 3 :=
  .composition .succ (fun _ : Fin 1 => .projection (1 : Fin 3))

/-- Literal original Program AST with inputs [x,y] and value x+y. -/
def addition : Program 2 := .recursion (.projection (0 : Fin 1)) additionStep

def multiplicationBase : Program 1 := .composition .zero Fin.elim0

/-- Add the fixed second factor to the previous result. -/
def multiplicationStep : Program 3 :=
  .composition addition (Fin.cons (.projection (1 : Fin 3))
    (Fin.cons (.projection (2 : Fin 3)) Fin.elim0))

/-- Literal original Program AST with inputs [x,y] and value x*y. -/
def multiplication : Program 2 := .recursion multiplicationBase multiplicationStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticPrograms
