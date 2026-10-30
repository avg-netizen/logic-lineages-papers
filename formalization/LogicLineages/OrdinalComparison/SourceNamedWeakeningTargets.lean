module
public import LogicLineages.OrdinalComparison.SourceNamedWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedWeakeningTargets
open SourceNamedSyntax SourceNamedWeakening

def ConcreteFreshName : Prop := ∀ Γ : Context,
    lookup Γ (freshName Γ) = none ∧ ∀ v ∈ Γ, v.1 < freshName Γ

def NamedRenamingIdentity : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    namedRename t (fun _ _ h => h) = t

def NamedRenamingErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (inc : NameInclusion Γ Δ) (ρ : Renaming (contextTypes Γ) (contextTypes Δ)),
    ResolutionAlong inc ρ → erase (namedRename t inc) = (erase t).rename ρ

def NamedRenamingFootprint : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (inc : NameInclusion Γ Δ),
    namedSupport (namedRename t inc) = namedSupport t ∧
    namedOccurrences (namedRename t inc) = namedOccurrences t ∧
    namedDepth (namedRename t inc) = namedDepth t

def ActualFreshWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (σ : Ty), ∃ hx : lookup Γ (freshName Γ) = none,
    ∀ (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    erase (namedWeaken (freshName Γ) σ hx t) =
      (erase t).rename (Renaming.weaken (contextTypes Γ) σ) ∧
    namedSupport (namedWeaken (freshName Γ) σ hx t) = namedSupport t ∧
    namedOccurrences (namedWeaken (freshName Γ) σ hx t) = namedOccurrences t ∧
    namedDepth (namedWeaken (freshName Γ) σ hx t) = namedDepth t
end LogicLineages.OrdinalComparison.Source.SourceNamedWeakeningTargets
