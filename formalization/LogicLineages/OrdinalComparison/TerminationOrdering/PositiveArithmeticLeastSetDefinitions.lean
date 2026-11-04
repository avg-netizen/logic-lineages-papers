module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsProof
public import Mathlib.Order.FixedPoints
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSet
open PositiveArithmeticOperators TaggedArithmeticOperators

/-- Metatheoretic standard-N operator on the complete powerset lattice. -/
def operator (body : Positive (Fin 2)) (context : Nat) : Set Nat →o Set Nat where
  toFun := fun P => {x | realize (fun y => y ∈ P) body.formula ![context,x]}
  monotone' := by
    intro P Q h x hx
    exact PositiveArithmeticOperatorsProof.positiveMonotonicity _ body (fun y => y ∈ P) (fun y => y ∈ Q) h _ hx

def leastSet (body : Positive (Fin 2)) (context : Nat) : Set Nat := (operator body context).lfp

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSet
