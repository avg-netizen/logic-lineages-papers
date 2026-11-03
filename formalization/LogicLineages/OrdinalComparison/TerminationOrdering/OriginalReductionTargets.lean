module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionTargets
open Source LiteralContexts

def RootOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ), RootReduction Symbol arity s t → ConfinedStrict above s t

def ContextualOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ), Reduction Symbol arity s t → ConfinedStrict above s t

def RootSubstitutionClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ) (θ : Substitution Symbol arity Γ Δ),
    RootReduction Symbol arity s t → RootReduction Symbol arity (s.substitute θ) (t.substitute θ)

def ContextualSubstitutionClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ) (θ : Substitution Symbol arity Γ Δ),
    Reduction Symbol arity s t → Reduction Symbol arity (s.substitute θ) (t.substitute θ)

def SubstitutedContextualOrientation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ Δ : List Ty) (τ : Ty) (s t : Term Symbol arity Γ τ) (θ : Substitution Symbol arity Γ Δ),
    Reduction Symbol arity s t → ConfinedStrict above (s.substitute θ) (t.substitute θ)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionTargets
