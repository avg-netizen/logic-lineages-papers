module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs are [predecessor, recursively computed result, initial state].
Only the recursive result is passed to the actual unary transition AST. -/
def repeatStep (transition : Program 1) : Program 3 :=
  .composition transition (fun _ : Fin 1 => .projection (1 : Fin 3))

/-- Ordinary numeric primitive recursion, with inputs [count, initial].
At the original stack transition this is literally the frozen stack iterate.
This is NOT the raw-list recursor and uses no encoded list or extra fuel. -/
def repeatProgram (transition : Program 1) : Program 2 :=
  .recursion (.projection (0 : Fin 1)) (repeatStep transition)

def repeatGraph {α : Type} (transition : Program 1)
    (out count initial : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (repeatProgram transition) out
    (Fin.cons count (Fin.cons initial Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIteration
