module

public import LogicLineages.OrdinalComparison.SourceMarkedBindingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedBindingTargets
open SourceMarkedSyntax SourceMarkedBinding

def MarkedRenamingIdentity : Prop :=
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q : MarkedTerm Symbol arity Γ τ), renameTerm q (fun v => v) = q) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ types : List Ty)
    (a : Arguments Symbol arity Γ types), renameArguments a (fun v => v) = a)

def MarkedSubstitutionIdentity : Prop :=
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q : MarkedTerm Symbol arity Γ τ), substituteTerm q (fun v => .var v) = q) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ types : List Ty)
    (a : Arguments Symbol arity Γ types), substituteArguments a (fun v => .var v) = a)

def EmbeddingRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (ρ : Renaming Γ Δ),
      embed (t.rename ρ) = renameTerm (embed t) ρ

def EmbeddingSubstitution : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (s : Substitution Symbol arity Γ Δ),
      embed (t.substitute s) = substituteTerm (embed t) (fun v => embed (s v))

end LogicLineages.OrdinalComparison.Source.SourceMarkedBindingTargets
