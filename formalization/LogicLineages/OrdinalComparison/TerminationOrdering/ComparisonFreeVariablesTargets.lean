module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceFreeOccurrences
open RecursiveComparison ComparisonFreeVariables

def OrdinaryOccurrenceCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ), markedOccurrences (embed t)=freeOccurrences t

def SupportCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) (q : MarkedTerm Symbol arity Γ τ) (a : Allowed Γ),
    Supported q a ↔ ∀ v ∈ markedOccurrences q, a v.2

def OriginalApplyProvenance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : List Ty) (σ τ : Ty) (types : List Ty) (q : MarkedTerm Symbol arity Γ σ)
    (env : MarkedSubstitution Symbol arity Γ Δ) (args : Arguments Symbol arity Δ types)
    (suffix : σ=arrows types τ) (r : MarkedTerm Symbol arity Δ τ) (a : Allowed Γ) (b : Allowed Δ),
    Supported q a → (∀ {υ} (v : Variable Γ υ),a v → Supported (env v) b) →
    ArgumentsSupported args b → applyOriginalWith q env args suffix=some r → Supported r b

def WeakFreeVariableContainment : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (s t : Packed Symbol arity Γ), Weak Symbol arity above Γ s t →
    ∀ v ∈ markedOccurrences t.2, v ∈ markedOccurrences s.2

def StrictFreeVariableContainment : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Γ : List Ty) (s t : Packed Symbol arity Γ), Strict Symbol arity above Γ s t →
    ∀ v ∈ markedOccurrences t.2, v ∈ markedOccurrences s.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesTargets
