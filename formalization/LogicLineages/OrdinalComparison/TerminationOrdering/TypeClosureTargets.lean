module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport

def LiteralEmbeddingTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ : List Ty) (τ : Ty) (q : Term Symbol arity Γ τ),
    SubtypeClosed K → (typesAllowed K (embed q) ↔ ∀ σ ∈ typeSupport q, K σ)

def RenamingTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ Δ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ) (ρ : Renaming Γ Δ),
    typesAllowed K q → typesAllowed K (renameTerm q ρ)

def MarkingTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ : List Ty) (τ : Ty) (q r : MarkedTerm Symbol arity Γ τ),
    typesAllowed K q → markSpine q = some r → typesAllowed K r

def SubstitutionTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ Δ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ)
    (env : MarkedSubstitution Symbol arity Γ Δ),
    typesAllowed K q → substitutionTypesAllowed K env → typesAllowed K (substituteTerm q env)

def SimultaneousApplicationTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ Δ : List Ty) (σ τ : Ty) (types : List Ty)
    (q : MarkedTerm Symbol arity Γ σ) (env : MarkedSubstitution Symbol arity Γ Δ)
    (args : Arguments Symbol arity Δ types) (h : σ = arrows types τ)
    (r : MarkedTerm Symbol arity Δ τ),
    SubtypeClosed K → typesAllowed K q → substitutionTypesAllowed K env →
    argumentTypesAllowed K args → applyOriginalWith q env args h = some r → typesAllowed K r

/-- Retyping is allowed only to a requested type already in K; base and extra
arguments are literally retained. -/
def RetypingTypeClosure : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (K : Ty → Prop)
    (Γ : List Ty) (h : Head Symbol) (σ τ : Ty)
    (base : Arguments Symbol arity Γ (headArguments arity h))
    (types : List Ty) (extras : Arguments Symbol arity Γ types),
    typesAllowed K (.marked h σ base types extras) → K τ →
    typesAllowed K (.marked h τ base types extras)

end LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureTargets
