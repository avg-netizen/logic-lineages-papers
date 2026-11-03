module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContexts
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison

inductive Context (Symbol : Type) (arity : Symbol → Nat) (Δ : List Ty) (υ : Ty) : List Ty → Ty → Type where
  | hole : Context Symbol arity Δ υ Δ υ
  | appFunction {Γ σ τ} : Context Symbol arity Δ υ Γ (.arrow σ τ) → Term Symbol arity Γ σ → Context Symbol arity Δ υ Γ τ
  | appArgument {Γ σ τ} : Term Symbol arity Γ (.arrow σ τ) → Context Symbol arity Δ υ Γ σ → Context Symbol arity Δ υ Γ τ
  | lam {Γ σ τ} : Context Symbol arity Δ υ (σ::Γ) τ → Context Symbol arity Δ υ Γ (.arrow σ τ)
  | ranked {Γ} (f : Symbol) (i : Fin (arity f)) (args : Fin (arity f) → Term Symbol arity Γ .ground) :
      Context Symbol arity Δ υ Γ .ground → Context Symbol arity Δ υ Γ .ground

def plug {Symbol : Type} {arity : Symbol → Nat} {Δ Γ : List Ty} {υ τ : Ty}
    (C : Context Symbol arity Δ υ Γ τ) (q : Term Symbol arity Δ υ) : Term Symbol arity Γ τ :=
  match C with
  | .hole => q
  | .appFunction C a => .app (plug C q) a
  | .appArgument f C => .app f (plug C q)
  | .lam C => .lam (plug C q)
  | .ranked f i args C => .ranked f (fun j => if j=i then plug C q else args j)

def ConfinedStrict {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Γ : List Ty} {τ : Ty} (s t : Term Symbol arity Γ τ) : Prop :=
  Strict Symbol arity above Γ ⟨τ,embed s⟩ ⟨τ,embed t⟩ ∧ typeSupport t ⊆ typeSupport s

open Source.SourceNamedSyntax
inductive NamedContext (Symbol : Type) (arity : Symbol → Nat) (Δ : SourceNamedSyntax.Context) (υ : Ty) :
    SourceNamedSyntax.Context → Ty → Type where
  | hole : NamedContext Symbol arity Δ υ Δ υ
  | appFunction {Γ σ τ} : NamedContext Symbol arity Δ υ Γ (.arrow σ τ) → NamedTerm Symbol arity Γ σ → NamedContext Symbol arity Δ υ Γ τ
  | appArgument {Γ σ τ} : NamedTerm Symbol arity Γ (.arrow σ τ) → NamedContext Symbol arity Δ υ Γ σ → NamedContext Symbol arity Δ υ Γ τ
  | lam {Γ σ τ} (x : Nat) : NamedContext Symbol arity Δ υ ((x,σ)::Γ) τ → NamedContext Symbol arity Δ υ Γ (.arrow σ τ)
  | ranked {Γ} (f : Symbol) (i : Fin (arity f)) (args : Fin (arity f) → NamedTerm Symbol arity Γ .ground) :
      NamedContext Symbol arity Δ υ Γ .ground → NamedContext Symbol arity Δ υ Γ .ground

def namedPlug {Symbol : Type} {arity : Symbol → Nat} {Δ Γ : SourceNamedSyntax.Context} {υ τ : Ty}
    (C : NamedContext Symbol arity Δ υ Γ τ) (q : NamedTerm Symbol arity Δ υ) : NamedTerm Symbol arity Γ τ :=
  match C with
  | .hole => q
  | .appFunction C a => .app (namedPlug C q) a
  | .appArgument f C => .app f (namedPlug C q)
  | .lam x C => .lam x (namedPlug C q)
  | .ranked f i args C => .ranked f (fun j => if j=i then namedPlug C q else args j)

def eraseContext {Symbol : Type} {arity : Symbol → Nat} {Δ Γ : SourceNamedSyntax.Context} {υ τ : Ty}
    (C : NamedContext Symbol arity Δ υ Γ τ) : Context Symbol arity (contextTypes Δ) υ (contextTypes Γ) τ :=
  match C with
  | .hole => .hole
  | .appFunction C a => .appFunction (eraseContext C) (erase a)
  | .appArgument f C => .appArgument (erase f) (eraseContext C)
  | .lam _ C => .lam (eraseContext C)
  | .ranked f i args C => .ranked f i (fun j => erase (args j)) (eraseContext C)

def NamedConfinedStrict {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {Γ : SourceNamedSyntax.Context} {τ : Ty} (s t : NamedTerm Symbol arity Γ τ) : Prop :=
  Strict Symbol arity above (contextTypes Γ) ⟨τ,embed (erase s)⟩ ⟨τ,embed (erase t)⟩ ∧ namedSupport t ⊆ namedSupport s

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContexts
