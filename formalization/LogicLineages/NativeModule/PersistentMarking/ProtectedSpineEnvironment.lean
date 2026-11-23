module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActions

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineEnvironment
open Spine NameBridge DecisionPorts HereditaryDomainCode HereditaryDomainSemantics

/-- Codes are rooted at the ambient context supplied to the interpreter. -/
abbrev FreeValues := List (Name × FiniteDomainSchema.Code)
abbrev BoundValues := List (Ty × FiniteDomainSchema.Code)

def lookupFree : FreeValues → Name → Option FiniteDomainSchema.Code
  | [], _ => none
  | (a,c)::rest, b => if a=b then some c else lookupFree rest b

def lookupBound (values : BoundValues) (σ : Ty) (i : Nat) : Option FiniteDomainSchema.Code := do
  let p ← values[i]?
  if p.1=σ then some p.2 else none

def weakenFree (E : Environment) (Γ Δ : Context) (values : FreeValues) : FreeValues :=
  values.map fun p => (p.1,(descriptor E p.1.1).restrict Γ Δ p.2)

def weakenBound (E : Environment) (Γ Δ : Context) (values : BoundValues) : BoundValues :=
  values.map fun p => (p.1,(descriptor E p.1).restrict Γ Δ p.2)

/-- A consumed prefix records origins in this call, never properties of codes. -/
def protectedLookup (consumed : Nat) (i : Nat) : Bool := decide (i < consumed)

/-- The choice depends on the observation context, not the source/root/family. -/
def openingSlot (Δ : Context) : Option Nat :=
  (List.range Δ.length).find? (fun i => decide (Δ[i]? = some none))

def openingContext (Δ : Context) (σ : Ty) (i : Nat) : Context :=
  Δ.zipIdx |>.map (fun p => if p.2=i then some σ else p.1)

def literal (E : Environment) (σ : Ty) (x : Nat) : Value where
  available _ := true
  weak _ t := FiniteDomainFoundation.exprEq (.free σ x) t
  strict _ _ := false
  application Δ _ τ _ := StructuralActions.bottom E τ Δ

def literalCode (E : Environment) (Γ : Context) (σ : Ty) (x : Nat) : FiniteDomainSchema.Code :=
  HereditaryDomainSemantics.encode E σ Γ (literal E σ x)

def freeCode (E : Environment) (Γ : Context) (values : FreeValues) (σ : Ty) (x : Nat) : FiniteDomainSchema.Code :=
  (lookupFree values (σ,x)).getD (literalCode E Γ σ x)

def boundCode (E : Environment) (Γ : Context) (values : BoundValues) (σ : Ty) (i : Nat) : FiniteDomainSchema.Code :=
  (lookupBound values σ i).getD (StructuralActions.bottom E σ Γ)

/-- Consume the literal full type tuple, not successive semantic calls. -/
def residualType : Ty → List Ty → Option Ty
  | σ, [] => some σ
  | .ground, _::_ => none
  | .arrow σ τ, ρ::ds => if σ=ρ then residualType τ ds else none

def originalHeadCall (E : Environment) (heads : List Head) (M : FiniteDomainSchema.Code) (Γ : Context)
    (f : Head) (σ : Ty) (base : List FiniteDomainSchema.Code) (extras : List MarkedExtras.Tagged)
    (domains : List Ty) (values : List FiniteDomainSchema.Code) (τ : Ty) : FiniteDomainSchema.Code :=
  if residualType σ domains = some τ ∧ domains.length=values.length then
    (StructuralActions.markedAction E heads M
      (f,τ,Γ,base,StructuralActions.insertExtras E Γ extras (domains.zip values))).getD
        (StructuralActions.bottom E τ Γ)
  else StructuralActions.bottom E τ Γ
end LogicLineages.PersistentMarking.ProtectedSpineEnvironment
