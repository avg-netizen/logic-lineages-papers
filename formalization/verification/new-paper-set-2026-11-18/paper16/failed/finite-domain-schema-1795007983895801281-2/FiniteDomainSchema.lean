import LogicLineages.PersistentMarking.FinitePrefixProof
namespace LogicLineages.PersistentMarking.FiniteDomainSchema
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainFoundation

abbrev Code := List Nat
/- Supporting callback only. The final builder must instantiate the same
canonical lower carrier independently of the current parent type. -/
abbrev LowerCarrier (σ : Ty) := (ρ : Ty) → typeSize ρ < typeSize σ → Context → List Code

inductive Kind where
  | available
  | weak : Expr → Kind
  | strict : Expr → Kind
  | application : List Ty → Ty → List Nat → Kind
structure Key where
  context : Context
  kind : Kind

/- Structural slot-extension test, including exhausted and zero-slot states. -/
def extendsBool : Context → Context → Bool
  | [],[] => true
  | none::Γ,_::Δ => extendsBool Γ Δ
  | some σ::Γ,some τ::Δ => decide (σ=τ) && extendsBool Γ Δ
  | _,_ => false

def extensions (K : List Ty) (B : Nat) (Γ : Context) : List Context :=
  (distinctContexts (contexts K B)).filter (extendsBool Γ)

def argumentBounds (σ : Ty) (lower : LowerCarrier σ) (Δ : Context)
    (domains : List Ty) (τ : Ty) (h : (domains,τ) ∈ fullPrefixes σ) : List Nat :=
  domains.attach.map (fun ρ => (lower ρ.val ((FinitePrefixProof.proper σ domains τ h).2 ρ.val ρ.property) Δ).length)

def outputBound (σ : Ty) (lower : LowerCarrier σ) (Δ : Context)
    (domains : List Ty) (τ : Ty) (h : (domains,τ) ∈ fullPrefixes σ) : Nat :=
  (lower τ (FinitePrefixProof.proper σ domains τ h).1 Δ).length

def atContext (σ : Ty) (lower : LowerCarrier σ) (V : List Name) (B : Nat)
    (target : Expr) (Δ : Context) : List (Key × Nat) :=
  [(⟨Δ,.available⟩,2)] ++
  (distinctObservations (observations V B Δ target σ)).map (fun t => (⟨Δ,.weak t⟩,2)) ++
  (distinctObservations (observations V B Δ target σ)).map (fun t => (⟨Δ,.strict t⟩,2)) ++
  (fullPrefixes σ).attach.flatMap (fun p =>
    (vectors (argumentBounds σ lower Δ p.val.1 p.val.2 p.property)).map
      (fun tuple => (⟨Δ,.application p.val.1 p.val.2 tuple⟩,
        outputBound σ lower Δ p.val.1 p.val.2 p.property)))

def schema (σ : Ty) (lower : LowerCarrier σ) (K : List Ty) (V : List Name)
    (B : Nat) (target : Expr) (Γ : Context) : List (Key × Nat) :=
  (extensions K B Γ).flatMap (atContext σ lower V B target)

def rawCodes (σ : Ty) (lower : LowerCarrier σ) (K : List Ty) (V : List Name)
    (B : Nat) (target : Expr) (Γ : Context) : List Code :=
  vectors ((schema σ lower K V B target Γ).map Prod.snd)

/- Literal semantic coordinate characterization, independent of success of
any comparison and of monotonicity/naturality of the supplied lower data. -/
def AtContextSpec (σ : Ty) (lower : LowerCarrier σ) (V : List Name) (B : Nat)
    (target : Expr) (Δ : Context) (key : Key) (bound : Nat) : Prop :=
  key.context = Δ ∧
    ((key.kind = .available ∧ bound=2) ∨
     (∃ t, t ∈ observations V B Δ target σ ∧ key.kind = .weak t ∧ bound=2) ∨
     (∃ t, t ∈ observations V B Δ target σ ∧ key.kind = .strict t ∧ bound=2) ∨
     (∃ domains τ (h : (domains,τ) ∈ fullPrefixes σ) tuple,
       Fits (argumentBounds σ lower Δ domains τ h) tuple ∧
       key.kind = .application domains τ tuple ∧ bound=outputBound σ lower Δ domains τ h))

def CoordinateSpec (σ : Ty) (lower : LowerCarrier σ) (K : List Ty) (V : List Name)
    (B : Nat) (target : Expr) (Γ : Context) (key : Key) (bound : Nat) : Prop :=
  ∃ Δ, WellFormed K B Δ ∧ Extends Γ Δ ∧ AtContextSpec σ lower V B target Δ key bound
end LogicLineages.PersistentMarking.FiniteDomainSchema
