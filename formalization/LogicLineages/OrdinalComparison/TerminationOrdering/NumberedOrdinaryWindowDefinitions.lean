module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindow
open Source Source.SourceMarkedSyntax Source.SourcePortContexts NumberedRewriteSyntax NumberedRewriteReduction

def symbols (n : Nat) : List (Fin n) := List.ofFn (fun i : Fin n => i)

def typeWindow {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (s : Term (Fin n) arity Gamma sigma) (t : Term (Fin n) arity Gamma tau) : List Ty :=
  literalTypes s ++ literalTypes t

def translated {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (t : Term (Fin n) arity Gamma tau) : Packed (Fin n) arity Gamma := ⟨tau,translateOriginal t⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOrdinaryWindow
