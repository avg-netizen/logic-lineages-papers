module

public import LogicLineages.OrdinalComparison.SourceMarkedSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMarkedSyntaxTargets
open SourceMarkedSyntax

def MarkSpineDomain : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q : MarkedTerm Symbol arity Γ τ), (markSpine q).isSome = (spineHead q).isSome

def MarkSpineHeadPreserved : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q r : MarkedTerm Symbol arity Γ τ), markSpine q = some r → spineHead r = spineHead q

def MarkSpineIdempotent : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (q : MarkedTerm Symbol arity Γ τ), (markSpine q).bind markSpine = markSpine q

def EmbeddingSpineCalibration : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ), spineHead (embed t) = originalSpineHead t

end LogicLineages.OrdinalComparison.Source.SourceMarkedSyntaxTargets
