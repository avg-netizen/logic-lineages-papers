module
public import LogicLineages.OrdinalComparison.SourceLocatedSubtermsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceLocatedSubtermsTargets
open SourceLocatedSubterms SourceTypeSupport

def LocatedRootMembership : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Ξ Λ : List Ty) (τ : Ty) (t : Term Symbol arity Ξ τ),
    (⟨Λ, Ξ, τ, t⟩ : LocatedTerm Symbol arity) ∈ collect Λ t

def LocatedChildClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Ξ Λ : List Ty) (τ : Ty) (t : Term Symbol arity Ξ τ)
    (u v : LocatedTerm Symbol arity),
    u ∈ collect Λ t → v ∈ children u → v ∈ collect Λ t

def LocatedTypeSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Ξ Λ : List Ty) (τ : Ty) (t : Term Symbol arity Ξ τ)
    (u : LocatedTerm Symbol arity),
    u ∈ collect Λ t → typeSupport u.body ⊆ typeSupport t

def LocatedDepthBudget : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Ξ Λ : List Ty) (τ : Ty) (t : Term Symbol arity Ξ τ)
    (u : LocatedTerm Symbol arity), u ∈ collect Λ t →
    u.binders.length + lambdaDepth u.body ≤ Λ.length + lambdaDepth t

def LocatedContextCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Ξ Λ Γ : List Ty) (τ : Ty) (t : Term Symbol arity Ξ τ), Ξ = Λ ++ Γ →
    ∀ u ∈ collect Λ t, u.ambient = u.binders ++ Γ
end LogicLineages.OrdinalComparison.Source.SourceLocatedSubtermsTargets
