module
public import LogicLineages.OrdinalComparison.TerminationOrdering.HeadClosureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Targets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication

def RenamingHeadClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (P : Head Symbol → Prop)
    (Γ Δ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ) (ρ : Renaming Γ Δ),
    headsAllowed P q → headsAllowed P (renameTerm q ρ)

def MarkingHeadClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (P : Head Symbol → Prop)
    (Γ : List Ty) (τ : Ty) (q r : MarkedTerm Symbol arity Γ τ),
    headsAllowed P q → markSpine q = some r → headsAllowed P r

def SubstitutionHeadClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (P : Head Symbol → Prop)
    (Γ Δ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ)
    (env : MarkedSubstitution Symbol arity Γ Δ),
    headsAllowed P q → substitutionAllowed P env → headsAllowed P (substituteTerm q env)

def SimultaneousApplicationHeadClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (P : Head Symbol → Prop)
    (Γ Δ : List Ty) (σ τ : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Γ σ) (env : MarkedSubstitution Symbol arity Γ Δ)
    (args : Arguments Symbol arity Δ types) (h : σ = arrows types τ)
    (r : MarkedTerm Symbol arity Δ τ),
    headsAllowed P q → substitutionAllowed P env → argumentsAllowed P args →
    applyOriginalWith q env args h = some r → headsAllowed P r

end LogicLineages.OrdinalComparison.TerminationOrdering.Targets
