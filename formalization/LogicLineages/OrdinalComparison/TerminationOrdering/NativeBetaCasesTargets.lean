module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesTargets
open Source LiteralContexts NativeBetaCases

def BetaConfinedOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (body : Term Symbol arity (σ::Γ) τ) (arg : Term Symbol arity Γ σ),
    ConfinedStrict above (.app (.lam body) arg) (body.substitute (Substitution.single arg))

def CaseFirstConfinedOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (u : Term Symbol arity Γ .ground) (A B : Term Symbol arity Γ τ),
    ConfinedStrict above (caseTerm u A B) A

def CaseSecondConfinedOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (u : Term Symbol arity Γ .ground) (A B : Term Symbol arity Γ τ),
    ConfinedStrict above (caseTerm u A B) B

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesTargets
