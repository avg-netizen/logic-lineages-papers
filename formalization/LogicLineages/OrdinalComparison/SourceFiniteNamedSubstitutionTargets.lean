module
public import LogicLineages.OrdinalComparison.SourceFiniteNamedSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitutionTargets
open SourceNamedSyntax SourceNamedSubstitution SourceFiniteNamedSubstitution

def FiniteNamedEntryEquations : Prop :=
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : Context)
    (a : Entry Symbol arity Γ) (rest : List (Entry Symbol arity Γ)),
    finiteEnvironment (a :: rest) a.name a.type a.valid = a.value) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : Context)
    (a : Entry Symbol arity Γ) (rest : List (Entry Symbol arity Γ))
    (x : Nat) (σ : Ty) (h : lookup Γ x = some σ), x ≠ a.name →
    finiteEnvironment (a :: rest) x σ h = finiteEnvironment rest x σ h) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : Context)
    (entries : List (Entry Symbol arity Γ)) (x : Nat) (σ : Ty)
    (h : lookup Γ x = some σ), (∀ a ∈ entries, a.name ≠ x) →
    finiteEnvironment entries x σ h = .var x h)

def NamedImageSupportMembership : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (env : NamedEnvironment Symbol arity Γ Δ) (vs : List (Nat × Ty)) (τ : Ty),
    τ ∈ namedImageSupport env vs ↔
      ∃ v ∈ vs, ∃ h : lookup Γ v.1 = some v.2, τ ∈ namedSupport (env v.1 v.2 h)

def ActualNamedSupportSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (env : NamedEnvironment Symbol arity Γ Δ),
    namedSupport (namedSubstitute t env) = namedSupport t ∪ namedImageSupport env (namedOccurrences t)

/-- Exact paper06 lem:supportsub on actual finite, type-preserving named entries.
The ambient context may contain any additional replacement free names. -/
def FullFiniteNamedSupportSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (entries : List (Entry Symbol arity Γ)),
    namedSupport (finiteNamedSubstitute t entries) =
      namedSupport t ∪ namedImageSupport (finiteEnvironment entries) (namedOccurrences t)
end LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitutionTargets
