module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedTree
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison

/-- The actual first-order ranked algebra: only ground variables and finite
ranked nodes. Native constants, applications, lambdas and marks are absent. -/
inductive Tree (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) : Type where
  | var : Variable Gamma .ground → Tree Symbol arity Gamma
  | node (f : Symbol) : (Fin (arity f) → Tree Symbol arity Gamma) → Tree Symbol arity Gamma

def ordinary {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    Tree Symbol arity Gamma → Term Symbol arity Gamma .ground
  | .var v => .var v
  | .node f args => .ranked f (fun i => ordinary (args i))

def markedSyntax {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    Tree Symbol arity Gamma → MarkedTerm Symbol arity Gamma .ground
  | .var v => .var v
  | .node f args => .ordinary (.ranked f) (groundArguments (arity f) (fun i => markedSyntax (args i)))

def pack {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (t : Tree Symbol arity Gamma) : Packed Symbol arity Gamma := ⟨.ground,markedSyntax t⟩

def markedRoot {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (f : Symbol) (args : Fin (arity f) → Tree Symbol arity Gamma) : Packed Symbol arity Gamma :=
  ⟨.ground,.marked (.ranked f) .ground
    (groundArguments (arity f) (fun i => markedSyntax (args i))) [] .nil⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedTree
