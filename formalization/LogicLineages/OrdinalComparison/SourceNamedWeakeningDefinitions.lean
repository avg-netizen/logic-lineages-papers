module
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxDefinitions
@[expose] public section
/-! Name-preserving context inclusion and actual fresh weakening. No named
substitution is obtained by quoting a kernel substitution. -/
namespace LogicLineages.OrdinalComparison.Source.SourceNamedWeakening
open SourceNamedSyntax

def freshName (Γ : Context) : Nat := (Γ.map Prod.fst).foldr max 0 + 1
abbrev NameInclusion (Γ Δ : Context) := ∀ (x : Nat) (σ : Ty),
  lookup Γ x = some σ → lookup Δ x = some σ

def liftInclusion {Γ Δ : Context} (inc : NameInclusion Γ Δ) (x : Nat) (σ : Ty) :
    NameInclusion ((x, σ) :: Γ) ((x, σ) :: Δ) := by
  intro y τ h
  by_cases e : y = x
  · simpa only [lookup, if_pos e] using h
  · simpa only [lookup, if_neg e] using inc y τ (by simpa only [lookup, if_neg e] using h)

def namedRename {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) {Δ : Context} (inc : NameInclusion Γ Δ) :
    NamedTerm Symbol arity Δ τ :=
  match t with
  | .var x h => .var x (inc x _ h)
  | .app f a => .app (namedRename f inc) (namedRename a inc)
  | .lam x body => .lam x (namedRename body (liftInclusion inc x _))
  | .zeroC => .zeroC
  | .succC => .succC
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .ranked s args => .ranked s (fun i => namedRename (args i) inc)

def ResolutionAlong {Γ Δ : Context} (inc : NameInclusion Γ Δ)
    (ρ : Renaming (contextTypes Γ) (contextTypes Δ)) : Prop :=
  ∀ (x : Nat) (σ : Ty) (h : lookup Γ x = some σ),
    resolve Δ x (inc x σ h) = ρ (resolve Γ x h)

def weakenInclusion {Γ : Context} (x : Nat) (σ : Ty) (hx : lookup Γ x = none) :
    NameInclusion Γ ((x, σ) :: Γ) := by
  intro y τ hy
  have hne : y ≠ x := by intro e; subst y; rw [hx] at hy; cases hy
  simpa only [lookup, if_neg hne] using hy

def namedWeaken {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (x : Nat) (σ : Ty) (hx : lookup Γ x = none) (t : NamedTerm Symbol arity Γ τ) :
    NamedTerm Symbol arity ((x, σ) :: Γ) τ := namedRename t (weakenInclusion x σ hx)

end LogicLineages.OrdinalComparison.Source.SourceNamedWeakening
