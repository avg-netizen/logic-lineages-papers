module
public import LogicLineages.OrdinalComparison.SourceNamedSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSubstitutionTargets
open SourceNamedSyntax SourceNamedWeakening SourceNamedWeakeningProof SourceNamedSubstitution

def ConstructedEnvironmentCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (env : NamedEnvironment Symbol arity Γ Δ),
    EnvironmentAlong env (kernelEnvironment env)

def NamedSubstitutionErasureSupplier : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (env : NamedEnvironment Symbol arity Γ Δ)
    (s : Substitution Symbol arity (contextTypes Γ) (contextTypes Δ)),
    EnvironmentAlong env s → erase (namedSubstitute t env) = (erase t).substitute s

def ActualNamedSubstitutionErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ Δ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ)
    (env : NamedEnvironment Symbol arity Γ Δ),
    erase (namedSubstitute t env) = (erase t).substitute (kernelEnvironment env)

def LiteralNamedSubstitutionEquations : Prop :=
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : Context) (τ : Ty)
    (x : Nat) (h : lookup Γ x = some τ) (env : NamedEnvironment Symbol arity Γ Δ),
    namedSubstitute (.var x h) env = env x τ h) ∧
  (∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : Context) (σ τ : Ty)
    (x : Nat) (body : NamedTerm Symbol arity ((x, σ) :: Γ) τ)
    (env : NamedEnvironment Symbol arity Γ Δ),
    namedSubstitute (.lam x body) env = .lam (freshName Δ)
      (namedSubstitute body (extendNamedEnvironment env x σ (freshName Δ) (concreteFreshName Δ).1)))

def IdentityNamedSubstitutionFootprint : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Γ : Context) (τ : Ty) (t : NamedTerm Symbol arity Γ τ),
    let u := namedSubstitute t (fun x _ h => .var x h)
    namedSupport u = namedSupport t ∧ namedOccurrences u = namedOccurrences t ∧
    namedDepth u = namedDepth t
end LogicLineages.OrdinalComparison.Source.SourceNamedSubstitutionTargets
