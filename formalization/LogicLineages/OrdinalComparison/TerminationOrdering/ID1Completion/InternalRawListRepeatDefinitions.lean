module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeat
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs are [head, recursively computed tail result, initial state].
The literal head and the initial-state parameter are ignored by this step. -/
def repeatStep (transition : Program 1) : Program 3 :=
  .composition transition (fun _ : Fin 1 => .projection 1)

/-- The unchanged raw-list recursor applies the unary transition once per
cell. Inputs are [raw list code, initial state]; no rank or fuel is supplied. -/
def repeatProgram (transition : Program 1) : Program 2 :=
  listRec (.projection (0 : Fin 1)) (repeatStep transition)

def repeatGraph {α : Type} (transition : Program 1)
    (out code initial : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (repeatProgram transition) out
    (Fin.cons code (Fin.cons initial Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeat
