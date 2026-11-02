module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorTargets
open Source NativeRecursor LiteralContexts

def ZeroConfinedOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (Γ : List Ty) (τ : Ty)
    (A : Term Symbol arity Γ (stepType τ)) (B : Term Symbol arity Γ τ),
    ConfinedStrict above (recursorTerm .zeroC A B) B

def SuccessorConfinedOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop) (Γ : List Ty) (τ : Ty)
    (n : Term Symbol arity Γ .ground) (A : Term Symbol arity Γ (stepType τ)) (B : Term Symbol arity Γ τ),
    ConfinedStrict above (recursorTerm (.app .succC n) A B) (successorContractum n A B)

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorTargets
