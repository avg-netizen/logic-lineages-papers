module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Structural compiler into the ordinary arithmetic language. No semantic
program symbol occurs in the resulting formula. Output is free index0, and
the n inputs occur at successor indices. -/
def graphFormula : {n : Nat} → Program n → Formula (Fin (n + 1))
  | _, .zero => zeroTerm.equal (.var 0)
  | _, .succ => (succTerm (.var 1)).equal (.var 0)
  | _, .projection i => (FirstOrder.Language.Term.var i.succ).equal (.var 0)
  | _, .composition f g => compositionGraph (graphFormula f) (fun i => graphFormula (g i))
  | _, .recursion f g => recursionGraph (graphFormula f) (graphFormula g)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic
