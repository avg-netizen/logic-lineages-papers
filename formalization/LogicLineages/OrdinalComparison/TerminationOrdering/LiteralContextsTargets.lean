module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsTargets
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport Source.SourceNamedSyntax RecursiveComparison LiteralContexts

def StrictMultisetFromStrictMatch : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (ss ts : List (Packed Symbol arity Γ)), WeakMatch Symbol arity above Γ ss ts →
    (∃ s t, (s,t) ∈ ss.zip ts ∧ Strict Symbol arity above Γ s t) → StrictMultiset Symbol arity above Γ ss ts

def ActualZeroArgumentSelect : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (τ : Ty) (q t : MarkedTerm Symbol arity Γ τ),
    (⟨τ,q⟩ : Packed Symbol arity Γ) ∈ argumentList base++argumentList extras → Weak Symbol arity above Γ ⟨τ,q⟩ ⟨τ,t⟩ →
    Weak Symbol arity above Γ ⟨τ,.marked f τ base types extras⟩ ⟨τ,t⟩

def OrdinaryHeadStrictCongruence : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (f : Head Symbol) (ss ts : Arguments Symbol arity Γ (headArguments arity f)),
    WeakMatch Symbol arity above Γ (argumentList ss) (argumentList ts) →
    (∃ s t, (s,t) ∈ (argumentList ss).zip (argumentList ts) ∧ Strict Symbol arity above Γ s t) →
    Strict Symbol arity above Γ ⟨_,.ordinary f ss⟩ ⟨_,.ordinary f ts⟩

def LambdaStrictCongruence : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (σ τ : Ty) (s t : MarkedTerm Symbol arity (σ::Γ) τ),
    Strict Symbol arity above (σ::Γ) ⟨τ,s⟩ ⟨τ,t⟩ → Strict Symbol arity above Γ ⟨.arrow σ τ,.lam s⟩ ⟨.arrow σ τ,.lam t⟩

def LiteralContextStrictClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Δ Γ : List Ty) (υ τ : Ty) (C : LiteralContexts.Context Symbol arity Δ υ Γ τ) (s t : Term Symbol arity Δ υ),
    Strict Symbol arity above Δ ⟨υ,embed s⟩ ⟨υ,embed t⟩ →
    Strict Symbol arity above Γ ⟨τ,embed (plug C s)⟩ ⟨τ,embed (plug C t)⟩

def LiteralContextSupportMonotonicity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Δ Γ : List Ty) (υ τ : Ty) (C : LiteralContexts.Context Symbol arity Δ υ Γ τ) (s t : Term Symbol arity Δ υ),
    typeSupport t ⊆ typeSupport s → typeSupport (plug C t) ⊆ typeSupport (plug C s)

def LiteralConfinedContextClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Δ Γ : List Ty) (υ τ : Ty) (C : LiteralContexts.Context Symbol arity Δ υ Γ τ) (s t : Term Symbol arity Δ υ),
    ConfinedStrict above s t → ConfinedStrict above (plug C s) (plug C t)

def NamedContextErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Δ Γ : SourceNamedSyntax.Context) (υ τ : Ty) (C : NamedContext Symbol arity Δ υ Γ τ) (s : NamedTerm Symbol arity Δ υ),
    erase (namedPlug C s)=plug (eraseContext C) (erase s)

def FullNamedContextStrictClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Δ Γ : SourceNamedSyntax.Context) (υ τ : Ty) (C : NamedContext Symbol arity Δ υ Γ τ) (s t : NamedTerm Symbol arity Δ υ),
    Strict Symbol arity above (contextTypes Δ) ⟨υ,embed (erase s)⟩ ⟨υ,embed (erase t)⟩ →
    Strict Symbol arity above (contextTypes Γ) ⟨τ,embed (erase (namedPlug C s))⟩ ⟨τ,embed (erase (namedPlug C t))⟩

def FullNamedConfinedContextClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Δ Γ : SourceNamedSyntax.Context) (υ τ : Ty) (C : NamedContext Symbol arity Δ υ Γ τ) (s t : NamedTerm Symbol arity Δ υ),
    NamedConfinedStrict above s t → NamedConfinedStrict above (namedPlug C s) (namedPlug C t)

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsTargets
