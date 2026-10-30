module
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSyntaxTargets
open SourceNamedSyntax SourceTypeSupport SourceFreeOccurrences

def NamedResolution : Prop := ∀ (Γ : Context) (x : Nat) (σ : Ty)
    (h : lookup Γ x = some σ),
    variableName (resolve Γ x h) = x ∧ Visible (resolve Γ x h)

def NamedSupportCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    typeSupport (erase t) = namedSupport t

def NamedOccurrenceTyping : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (v : Nat × Ty), v ∈ namedOccurrences t → lookup Γ v.1 = some v.2

def NamedOccurrenceCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    (freeOccurrences (erase t)).map namePacked = namedOccurrences t

def NamedDepthCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    lambdaDepth (erase t) = namedDepth t
end LogicLineages.OrdinalComparison.Source.SourceNamedSyntaxTargets
