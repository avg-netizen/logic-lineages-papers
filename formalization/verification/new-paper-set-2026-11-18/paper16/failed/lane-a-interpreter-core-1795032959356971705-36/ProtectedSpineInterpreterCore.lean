import LogicLineages.PersistentMarking.MarkedConstructorValue

namespace LogicLineages.PersistentMarking.ProtectedSpineInterpreterCore
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment
open MarkedFamilyParameters (Parameter)

def code (E : Environment) (σ : Ty) (Γ : Context) (v : Value) : Code := encode E σ Γ v

def parameter (E : Environment) (f : Head) (τ : Ty) (Γ : Context)
    (base extras : BoundValues) : Parameter :=
  (f,τ,Γ,base.map Prod.snd,MarkedExtras.down E Γ extras)

def funTest (S : Signature) (E : Environment) (p : Parameter) (t : Expr) : Bool :=
  match t with
  | .head g ts => MarkedConstructorTests.equivalent S p.1 g &&
      decide (p.2.1 = g.result) &&
      MarkedConstructorTests.matching E p.2.2.1 (p.1.arguments.zip p.2.2.2.1)
        (MarkedConstructorTests.terms ts)
  | _ => false

def ordinaryHead (S : Signature) (E : Environment) (heads : List Head) (M : Code) (p : Parameter) : Value :=
  let marked := MarkedConstructorValue.build S E heads M p
  { marked with weak := fun Δ t =>
      funTest S E (MarkedFamilyCoherence.weakenParameter E p Δ) t || marked.weak Δ t }

def variableCall (E : Environment) (σ : Ty) (Γ : Context) (c : Code)
    (domains : List Ty) (values : List Code) (τ : Ty) : Code :=
  if residualType σ domains = some τ ∧ domains.length = values.length then
    StructuralActions.fullAction E σ Γ c domains τ values
  else StructuralActions.bottom E τ Γ

/-- The two consumers of one original source expression. -/
structure Evaluation where
  value : Context → FreeValues → BoundValues → Value
  nonempty : Context → FreeValues → BoundValues → Nat →
    Ty → Code → List Ty → List Code → Ty → Code

def lambdaCall (E : Environment) (σ ρ : Ty) (body : Evaluation)
    (Γ : Context) (free : FreeValues) (bound : BoundValues) (consumed : Nat)
    (domain : Ty) (argument : Code) (domains : List Ty) (values : List Code) (τ : Ty) : Code :=
  if domain = σ then
    let next := (σ,argument)::bound
    match domains, values with
    | [], [] =>
      if ρ = τ then code E τ Γ (body.value Γ free next) else StructuralActions.bottom E τ Γ
    | d::ds, a::xs => body.nonempty Γ free next (consumed+1) d a ds xs τ
    | _, _ => StructuralActions.bottom E τ Γ
  else StructuralActions.bottom E τ Γ

def lambdaField (E : Environment) (σ : Ty) (body : Evaluation) (Γ : Context)
    (free : FreeValues) (bound : BoundValues) (strict : Bool) (Δ : Context) (t : Expr) : Bool :=
  match t with
  | .lam ρ target =>
    if σ = ρ then
      match openingSlot Δ with
      | none => false
      | some i =>
        let Θ := openingContext Δ σ i
        let x := portName E.names i
        let v := body.value Θ (weakenFree E Γ Θ free)
          ((σ,literalCode E Θ σ x)::weakenBound E Γ Θ bound)
        if strict then v.strict Θ (openBody σ x target) else v.weak Θ (openBody σ x target)
    else false
  | _ => false

def lambdaValue (E : Environment) (σ ρ : Ty) (body : Evaluation)
    (Γ : Context) (free : FreeValues) (bound : BoundValues) : Value where
  available _ := true
  weak := lambdaField E σ body Γ free bound false
  strict := lambdaField E σ body Γ free bound true
  application Δ domains τ values :=
    match domains, values with
    | d::ds, a::xs =>
      lambdaCall E σ ρ body Δ (weakenFree E Γ Δ free) (weakenBound E Γ Δ bound) 0 d a ds xs τ
    | _, _ => StructuralActions.bottom E τ Δ

end LogicLineages.PersistentMarking.ProtectedSpineInterpreterCore
