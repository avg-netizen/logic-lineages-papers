module
public import LogicLineages.OrdinalComparison.SourceNamedWeakeningProof
@[expose] public section
/-! Independent capture-avoiding recursion on named syntax. Fresh target binders
mask the original bound name; replacement images are actually weakened. -/
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSubstitution
open SourceNamedSyntax SourceNamedWeakening SourceNamedWeakeningProof

abbrev NamedEnvironment (Symbol : Type) (arity : Symbol → Nat) (Γ Δ : Context) :=
  ∀ (x : Nat) (σ : Ty), lookup Γ x = some σ → NamedTerm Symbol arity Δ σ

def canonicalInhabitant {Symbol : Type} {arity : Symbol → Nat} (Γ : List Ty) :
    (τ : Ty) → Term Symbol arity Γ τ
  | .ground => .zeroC
  | .arrow σ τ => .lam (canonicalInhabitant (σ :: Γ) τ)

def kernelEnvironment {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ) :
    Substitution Symbol arity (contextTypes Γ) (contextTypes Δ) :=
  fun {σ} v => if h : lookup Γ (variableName v) = some σ then
    erase (env (variableName v) σ h) else canonicalInhabitant (contextTypes Δ) σ

def EnvironmentAlong {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ)
    (s : Substitution Symbol arity (contextTypes Γ) (contextTypes Δ)) : Prop :=
  ∀ (x : Nat) (σ : Ty) (h : lookup Γ x = some σ), erase (env x σ h) = s (resolve Γ x h)

def extendNamedEnvironment {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ) (x : Nat) (σ : Ty)
    (y : Nat) (hy : lookup Δ y = none) :
    NamedEnvironment Symbol arity ((x, σ) :: Γ) ((y, σ) :: Δ) :=
  fun z τ h => if e : z = x then
    have ht : σ = τ := by simpa only [lookup, if_pos e, Option.some.injEq] using h
    ht ▸ NamedTerm.var y (by simp [lookup])
  else namedWeaken y σ hy (env z τ (by simpa only [lookup, if_neg e] using h))

def namedSubstitute {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) {Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ) : NamedTerm Symbol arity Δ τ :=
  match t with
  | .var x h => env x _ h
  | .app f a => .app (namedSubstitute f env) (namedSubstitute a env)
  | .lam x body => .lam (freshName Δ) (namedSubstitute body
      (extendNamedEnvironment env x _ (freshName Δ) (concreteFreshName Δ).1))
  | .zeroC => .zeroC
  | .succC => .succC
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .ranked s args => .ranked s (fun i => namedSubstitute (args i) env)

end LogicLineages.OrdinalComparison.Source.SourceNamedSubstitution
