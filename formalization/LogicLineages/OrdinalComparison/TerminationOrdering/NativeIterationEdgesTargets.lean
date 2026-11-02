module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesTargets
open Source LiteralContexts NativeIterationEdges

def BaseEdge : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (A : Ty) (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (U : Term Symbol arity [] (translatedType A)) (i : Term Symbol arity [] indexType),
    ConfinedStrict above (iterationCarrier A P U i) U

def IndexEdge : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (A : Ty) (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (U : Term Symbol arity [] (translatedType A)) (i j : Term Symbol arity [] indexType),
    ConfinedStrict above i j → ConfinedStrict above (iterationCarrier A P U i) (iterationCarrier A P U j)

def ApplicationEdge : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (A : Ty) (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (U : Term Symbol arity [] (translatedType A)) (i j : Term Symbol arity [] indexType),
    ConfinedStrict above i j → ConfinedStrict above (iterationCarrier A P U i) (.app P (iterationCarrier A P U j))

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesTargets
