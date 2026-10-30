module
public import LogicLineages.OrdinalComparison.SourceNamedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedPortsTargets
open SourceNamedSyntax SourceNamedWeakening SourcePortContexts SourceNamedPorts

def SpelledPortInjective : Prop := ∀ (Γ : Context) (B : Nat), Function.Injective (spellPort Γ (B := B))
def SpelledPortFresh : Prop := ∀ (Γ : Context) (B : Nat) (i : Fin B),
    ∀ p ∈ Γ, spellPort Γ i ≠ p.1

def RealizedPortTypes : Prop := ∀ (Γ : Context) (B : Nat) (P : PortContext B),
    contextTypes (realizedContext Γ P) = portTypes P ++ contextTypes Γ

def RealizedPortLookup : Prop := ∀ (Γ : Context) (B : Nat) (P : PortContext B),
    (P.map Prod.fst).Nodup →
    (∀ (x : Nat) (σ : Ty), lookup Γ x = some σ → lookup (realizedContext Γ P) x = some σ) ∧
    (∀ (i : Fin B) (σ : Ty), (i, σ) ∈ P → lookup (realizedContext Γ P) (spellPort Γ i) = some σ)

def RealizedFreshExtension : Prop := ∀ (Γ : Context) (B : Nat) (P : PortContext B)
    (i : Fin B) (σ : Ty), i ∉ P.map Prod.fst →
    lookup (realizedContext Γ P) (spellPort Γ i) = none ∧
    realizedContext Γ ((i, σ) :: P) = (spellPort Γ i, σ) :: realizedContext Γ P

def ActualNamedPortWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (B : Nat) (P : PortContext B) (i : Fin B) (σ : Ty),
    i ∉ P.map Prod.fst → ∃ h : lookup (realizedContext Γ P) (spellPort Γ i) = none,
    ∀ (τ : Ty) (t : NamedTerm Symbol arity (realizedContext Γ P) τ),
    erase (namedWeaken (spellPort Γ i) σ h t) =
      (erase t).rename (Renaming.weaken (contextTypes (realizedContext Γ P)) σ) ∧
    namedSupport (namedWeaken (spellPort Γ i) σ h t) = namedSupport t ∧
    namedOccurrences (namedWeaken (spellPort Γ i) σ h t) = namedOccurrences t ∧
    namedDepth (namedWeaken (spellPort Γ i) σ h t) = namedDepth t
end LogicLineages.OrdinalComparison.Source.SourceNamedPortsTargets
