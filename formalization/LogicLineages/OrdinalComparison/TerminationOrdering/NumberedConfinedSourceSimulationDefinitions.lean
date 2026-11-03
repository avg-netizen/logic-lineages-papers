module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulation
open Source Source.SourcePortContexts

/-- The literal type window of the original source alone. -/
def sourceWindow {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (s : Term (Fin n) arity Gamma tau) : List Ty :=
  literalTypes s

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedConfinedSourceSimulation
