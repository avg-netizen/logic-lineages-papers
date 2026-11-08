module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIteration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- For an arbitrary binary AST P with inputs [value, parameter], carry the
parameter in the LEFT coordinate of the original pair code. The only input
is the raw state. This literal AST is fixed before any symbolic parameter
is supplied: state maps to pair(left state, P(right state, left state)). -/
def carryP (P : Program 2) : Program 1 :=
  .composition InternalPairing.pairing
    (Fin.cons InternalUnpair.left
      (Fin.cons (.composition P
        (Fin.cons InternalUnpair.right (Fin.cons InternalUnpair.left Fin.elim0))) Fin.elim0))

/-- Inputs [count, value, parameter]. Form the actual initial pair
[parameter, value], run the existing numeric iterator on carryP P, then
return the actual right coordinate. There is no interpreter, specialized
parameter numeral, raw-list recursion, or new recursion primitive. -/
def repeatP (P : Program 2) : Program 3 :=
  .composition InternalUnpair.right (fun _ : Fin 1 =>
    .composition (InternalNumericIteration.repeatProgram (carryP P))
      (Fin.cons (.projection (0 : Fin 3))
        (Fin.cons (.composition InternalPairing.pairing
          (Fin.cons (.projection (2 : Fin 3))
            (Fin.cons (.projection (1 : Fin 3)) Fin.elim0))) Fin.elim0)))

def carryGraph {α : Type} (P : Program 2)
    (out state : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (carryP P) out (Fin.cons state Fin.elim0)

def repeatGraph {α : Type} (P : Program 2)
    (out count value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (repeatP P) out
    (Fin.cons count (Fin.cons value (Fin.cons parameter Fin.elim0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIteration
