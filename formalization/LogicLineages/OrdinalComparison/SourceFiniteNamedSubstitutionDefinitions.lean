module
public import LogicLineages.OrdinalComparison.SourceNamedSubstitutionDefinitions
@[expose] public section
/-! Literal finite named substitution entries. The common finite ambient context
contains all source and replacement free names, not only the source's FV.
First matching entry wins; missing names retain their original variables. -/
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitution
open SourceNamedSyntax SourceNamedSubstitution

structure Entry (Symbol : Type) (arity : Symbol → Nat) (Γ : Context) where
  name : Nat
  type : Ty
  valid : lookup Γ name = some type
  value : NamedTerm Symbol arity Γ type

def finiteEnvironment {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} :
    List (Entry Symbol arity Γ) → NamedEnvironment Symbol arity Γ Γ
  | [] => fun x _ h => .var x h
  | a :: rest => fun x σ h => if e : x = a.name then
      have hh : lookup Γ a.name = some σ := by simpa only [e] using h
      have ht : a.type = σ := Option.some.inj (a.valid.symm.trans hh)
      ht ▸ a.value
    else finiteEnvironment rest x σ h

def namedImageSupport {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ) : List (Nat × Ty) → Finset Ty
  | [] => ∅
  | (x, σ) :: rest => (if h : lookup Γ x = some σ then namedSupport (env x σ h) else ∅) ∪
      namedImageSupport env rest

def finiteNamedSubstitute {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) (entries : List (Entry Symbol arity Γ)) :
    NamedTerm Symbol arity Γ τ := namedSubstitute t (finiteEnvironment entries)

end LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitution
