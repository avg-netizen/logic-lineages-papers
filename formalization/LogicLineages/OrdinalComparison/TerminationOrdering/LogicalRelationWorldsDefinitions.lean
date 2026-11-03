module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorlds
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits LiteralVariableValue

/-- The actual typed port transport, without an assumed list order. -/
def portRename {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    {P Q : World I} (h : Extends P Q) : Renaming (portTypes P.val++I.context) (portTypes Q.val++I.context) :=
  extendVariables I.context Q.val P.val h

end LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorlds
