module

public import LogicLineages.NativeModule.PersistentMarking.FiniteDomainSchema

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryDomainCode
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema

structure Environment where
  types : List Ty
  names : List Name
  ports : Nat
  target : Expr

structure Descriptor where
  carriers : Context → List Code
  le : Context → Code → Code → Bool
  restrict : Context → Context → Code → Code
  join : Context → List Code → Code
  meet : Context → List Code → Code

abbrev Lower (σ : Ty) := (ρ : Ty) → typeSize ρ < typeSize σ → Descriptor

def lowerCodes (σ : Ty) (lower : Lower σ) : LowerCarrier σ :=
  fun ρ hp Γ => (lower ρ hp).carriers Γ

def kindEq : Kind → Kind → Bool
  | .available,.available => true
  | .weak q,.weak r | .strict q,.strict r => exprEq q r
  | .application ds τ xs,.application es υ ys => decide (ds=es) && decide (τ=υ) && decide (xs=ys)
  | _,_ => false

def keyEq (a b : Key) : Bool := decide (a.context=b.context) && kindEq a.kind b.kind

def lookup : List (Key × Nat) → Code → Key → Option Nat
  | (k,_)::ks,v::vs,key => if keyEq k key then some v else lookup ks vs key
  | _,_,_ => none

def indexOf (codes : List Code) (value : Code) : Option Nat :=
  match codes with
  | [] => none
  | c::cs => if decide (c=value) then some 0 else (indexOf cs value).map Nat.succ

def layout (E : Environment) (σ : Ty) (lower : Lower σ) (Γ : Context) : List (Key × Nat) :=
  schema σ (lowerCodes σ lower) E.types E.names E.ports E.target Γ

def project (E : Environment) (σ : Ty) (lower : Lower σ) (Γ Θ : Context) (code : Code) : Code :=
  (layout E σ lower Θ).map (fun kb => (lookup (layout E σ lower Γ) code kb.1).getD 0)

abbrev Prefix (σ : Ty) := {p : List Ty × Ty // p ∈ fullPrefixes σ}

def tupleBounds (σ : Ty) (lower : Lower σ) (Δ : Context) (p : Prefix σ) : List Nat :=
  argumentBounds σ (lowerCodes σ lower) Δ p.val.1 p.val.2 p.property

def resultDescriptor (σ : Ty) (lower : Lower σ) (p : Prefix σ) : Descriptor :=
  lower p.val.2 (FinitePrefixProof.proper σ p.val.1 p.val.2 p.property).1

def tupleDecode (σ : Ty) (lower : Lower σ) (Δ : Context) (p : Prefix σ) (tuple : List Nat) : Option (List Code) :=
  if tuple.length = p.val.1.length then
    (p.val.1.attach.zip tuple).mapM (fun pair =>
      ((lower pair.1.val ((FinitePrefixProof.proper σ p.val.1 p.val.2 p.property).2 pair.1.val pair.1.property)).carriers Δ)[pair.2]?)
  else none

def tupleLe (σ : Ty) (lower : Lower σ) (Δ : Context) (p : Prefix σ) (xs ys : List Nat) : Bool :=
  match tupleDecode σ lower Δ p xs,tupleDecode σ lower Δ p ys with
  | some as_,some bs =>
      (p.val.1.attach.zip (as_.zip bs)).all (fun pair =>
        (lower pair.1.val ((FinitePrefixProof.proper σ p.val.1 p.val.2 p.property).2 pair.1.val pair.1.property)).le Δ pair.2.1 pair.2.2)
  | _,_ => false

def tupleRestrict (σ : Ty) (lower : Lower σ) (Δ Θ : Context) (p : Prefix σ) (xs : List Nat) : Option (List Nat) :=
  match tupleDecode σ lower Δ p xs with
  | none => none
  | some vs => (p.val.1.attach.zip vs).mapM (fun pair =>
      let D := lower pair.1.val ((FinitePrefixProof.proper σ p.val.1 p.val.2 p.property).2 pair.1.val pair.1.property)
      indexOf (D.carriers Θ) (D.restrict Δ Θ pair.2))

def output (E : Environment) (σ : Ty) (lower : Lower σ) (Γ Δ : Context)
    (p : Prefix σ) (tuple : List Nat) (code : Code) : Option Code := do
  let i ← lookup (layout E σ lower Γ) code ⟨Δ,.application p.val.1 p.val.2 tuple⟩
  ((resultDescriptor σ lower p).carriers Δ)[i]?

def monotone (E : Environment) (σ : Ty) (lower : Lower σ) (Γ : Context) (code : Code) : Bool :=
  (extensions E.types E.ports Γ).all (fun Δ => (fullPrefixes σ).attach.all (fun p =>
    (vectors (tupleBounds σ lower Δ p)).all (fun xs =>
      (vectors (tupleBounds σ lower Δ p)).all (fun ys =>
        if tupleLe σ lower Δ p xs ys then
          match output E σ lower Γ Δ p xs code,output E σ lower Γ Δ p ys code with
          | some a,some b => (resultDescriptor σ lower p).le Δ a b
          | _,_ => false
        else true))))

def natural (E : Environment) (σ : Ty) (lower : Lower σ) (Γ : Context) (code : Code) : Bool :=
  (extensions E.types E.ports Γ).all (fun Δ =>
    (extensions E.types E.ports Δ).all (fun Θ => (fullPrefixes σ).attach.all (fun p =>
      (vectors (tupleBounds σ lower Δ p)).all (fun xs =>
        match tupleRestrict σ lower Δ Θ p xs,output E σ lower Γ Δ p xs code with
        | some ys,some a => match output E σ lower Γ Θ p ys code with
          | some b => decide ((resultDescriptor σ lower p).restrict Δ Θ a = b)
          | none => false
        | _,_ => false))))

def codeLe (E : Environment) (σ : Ty) (lower : Lower σ) (Γ : Context) (a b : Code) : Bool :=
  (extensions E.types E.ports Γ).all (fun Δ =>
    let bits := [Kind.available] ++
      (distinctObservations (observations E.names E.ports Δ E.target σ)).map Kind.weak ++
      (distinctObservations (observations E.names E.ports Δ E.target σ)).map Kind.strict
    bits.all (fun k => match lookup (layout E σ lower Γ) a ⟨Δ,k⟩,lookup (layout E σ lower Γ) b ⟨Δ,k⟩ with
      | some i,some j => decide (i≤j)
      | _,_ => false) &&
    (fullPrefixes σ).attach.all (fun p => (vectors (tupleBounds σ lower Δ p)).all (fun xs =>
      match output E σ lower Γ Δ p xs a,output E σ lower Γ Δ p xs b with
      | some v,some w => (resultDescriptor σ lower p).le Δ v w
      | _,_ => false)))

def bitCombine (meet : Bool) (xs : List Nat) : Nat :=
  if meet then xs.foldl Nat.min 1 else xs.foldl Nat.max 0

def combineAt (E : Environment) (σ : Ty) (lower : Lower σ) (Γ Δ : Context)
    (meet : Bool) (codes : List Code) : Code :=
  let bits := [Kind.available] ++
    (distinctObservations (observations E.names E.ports Δ E.target σ)).map Kind.weak ++
    (distinctObservations (observations E.names E.ports Δ E.target σ)).map Kind.strict
  bits.map (fun k => bitCombine meet (codes.map (fun c => (lookup (layout E σ lower Γ) c ⟨Δ,k⟩).getD 0))) ++
  (fullPrefixes σ).attach.flatMap (fun p => (vectors (tupleBounds σ lower Δ p)).map (fun xs =>
    let D := resultDescriptor σ lower p
    let values := codes.filterMap (output E σ lower Γ Δ p xs)
    (indexOf (D.carriers Δ) (if meet then D.meet Δ values else D.join Δ values)).getD 0))

def combine (E : Environment) (σ : Ty) (lower : Lower σ) (Γ : Context)
    (meet : Bool) (codes : List Code) : Code :=
  (extensions E.types E.ports Γ).flatMap (fun Δ => combineAt E σ lower Γ Δ meet codes)

def build (E : Environment) (σ : Ty) (lower : Lower σ) : Descriptor where
  carriers Γ := (rawCodes σ (lowerCodes σ lower) E.types E.names E.ports E.target Γ).filter
    (fun c => monotone E σ lower Γ c && natural E σ lower Γ c)
  le := codeLe E σ lower
  restrict := project E σ lower
  join Γ := combine E σ lower Γ false
  meet Γ := combine E σ lower Γ true

def descriptor (E : Environment) (σ : Ty) : Descriptor :=
  build E σ (fun ρ h => descriptor E ρ)
termination_by typeSize σ

end LogicLineages.PersistentMarking.HereditaryDomainCode
