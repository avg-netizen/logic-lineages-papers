module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryDomainCode

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryDomainSemantics
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode

structure Value where
  available : Context → Bool
  weak : Context → Expr → Bool
  strict : Context → Expr → Bool
  application : Context → List Ty → Ty → List Code → Code

def TupleValues (E : Environment) (Δ : Context) (domains : List Ty) (values : List Code) : Prop :=
  domains.length = values.length ∧ ∀ (i : Nat) (ρ : Ty) (v : Code),
    domains[i]? = some ρ → values[i]? = some v → v ∈ (descriptor E ρ).carriers Δ

def ValuesLE (E : Environment) (Δ : Context) (domains : List Ty) (xs ys : List Code) : Prop :=
  ∀ (i : Nat) (ρ : Ty) (x y : Code), domains[i]? = some ρ → xs[i]? = some x → ys[i]? = some y →
    (descriptor E ρ).le Δ x y = true

def restrictValues (E : Environment) (Δ Θ : Context) (domains : List Ty) (values : List Code) : List Code :=
  (domains.zip values).map (fun p => (descriptor E p.1).restrict Δ Θ p.2)

/- Only actual coordinates matter. Off-schema values are not independent
semantic bits; ValueEq below quotients them extensionally. -/
def Valid (E : Environment) (σ : Ty) (Γ : Context) (v : Value) : Prop :=
  (∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ → ∀ domains τ,
    (domains,τ) ∈ fullPrefixes σ → ∀ xs, TupleValues E Δ domains xs →
      v.application Δ domains τ xs ∈ (descriptor E τ).carriers Δ) ∧
  (∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ → ∀ domains τ,
    (domains,τ) ∈ fullPrefixes σ → ∀ xs ys,
      TupleValues E Δ domains xs → TupleValues E Δ domains ys → ValuesLE E Δ domains xs ys →
      (descriptor E τ).le Δ (v.application Δ domains τ xs) (v.application Δ domains τ ys) = true) ∧
  (∀ Δ Θ, WellFormed E.types E.ports Δ → WellFormed E.types E.ports Θ →
    Extends Γ Δ → Extends Δ Θ → ∀ domains τ, (domains,τ) ∈ fullPrefixes σ →
    ∀ xs, TupleValues E Δ domains xs →
      (descriptor E τ).restrict Δ Θ (v.application Δ domains τ xs) =
        v.application Θ domains τ (restrictValues E Δ Θ domains xs))

def ValueEq (E : Environment) (σ : Ty) (Γ : Context) (a b : Value) : Prop :=
  ∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ →
    a.available Δ = b.available Δ ∧
    (∀ t, t ∈ observations E.names E.ports Δ E.target σ → a.weak Δ t = b.weak Δ t ∧ a.strict Δ t = b.strict Δ t) ∧
    (∀ domains τ, (domains,τ) ∈ fullPrefixes σ → ∀ xs, TupleValues E Δ domains xs →
      a.application Δ domains τ xs = b.application Δ domains τ xs)

def canonicalLower (E : Environment) (σ : Ty) : Lower σ := fun ρ _ => descriptor E ρ

def indices (E : Environment) (Δ : Context) (domains : List Ty) (values : List Code) : Option (List Nat) :=
  if domains.length = values.length then
    (domains.zip values).mapM (fun p => indexOf ((descriptor E p.1).carriers Δ) p.2)
  else none

def values (E : Environment) (Δ : Context) (domains : List Ty) (tuple : List Nat) : Option (List Code) :=
  if domains.length = tuple.length then
    (domains.zip tuple).mapM (fun p => ((descriptor E p.1).carriers Δ)[p.2]?)
  else none

def decode (E : Environment) (σ : Ty) (Γ : Context) (code : Code) : Value where
  available Δ := (lookup (layout E σ (canonicalLower E σ) Γ) code ⟨Δ,.available⟩).getD 0 == 1
  weak Δ t := (lookup (layout E σ (canonicalLower E σ) Γ) code ⟨Δ,.weak t⟩).getD 0 == 1
  strict Δ t := (lookup (layout E σ (canonicalLower E σ) Γ) code ⟨Δ,.strict t⟩).getD 0 == 1
  application Δ domains τ xs :=
    ((do
      let tuple ← indices E Δ domains xs
      let i ← lookup (layout E σ (canonicalLower E σ) Γ) code ⟨Δ,.application domains τ tuple⟩
      ((descriptor E τ).carriers Δ)[i]?) : Option Code).getD []

def encode (E : Environment) (σ : Ty) (Γ : Context) (v : Value) : Code :=
  (layout E σ (canonicalLower E σ) Γ).map (fun kb =>
    let Δ := kb.1.context
    match kb.1.kind with
    | .available => if v.available Δ then 1 else 0
    | .weak t => if v.weak Δ t then 1 else 0
    | .strict t => if v.strict Δ t then 1 else 0
    | .application domains τ tuple =>
      ((do
        let xs ← values E Δ domains tuple
        indexOf ((descriptor E τ).carriers Δ) (v.application Δ domains τ xs)) : Option Nat).getD 0)
end LogicLineages.PersistentMarking.HereditaryDomainSemantics
