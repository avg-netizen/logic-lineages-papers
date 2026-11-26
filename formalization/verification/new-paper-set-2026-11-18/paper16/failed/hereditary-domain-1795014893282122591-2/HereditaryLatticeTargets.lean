import LogicLineages.PersistentMarking.HereditaryOrderTargets
namespace LogicLineages.PersistentMarking.HereditaryLatticeTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets

/- Actual pointwise values. Empty joins have false bits and empty meets true
bits. Every application calls the global residual descriptor, not a supplied
operation or parent-dependent lower carrier. -/
def aggregate (E : Environment) (meet : Bool) (xs : List Value) : Value where
  available Δ := if meet then xs.all (fun v => v.available Δ) else xs.any (fun v => v.available Δ)
  weak Δ t := if meet then xs.all (fun v => v.weak Δ t) else xs.any (fun v => v.weak Δ t)
  strict Δ t := if meet then xs.all (fun v => v.strict Δ t) else xs.any (fun v => v.strict Δ t)
  application Δ ds τ vs :=
    if meet then (descriptor E τ).meet Δ (xs.map (fun v => v.application Δ ds τ vs))
    else (descriptor E τ).join Δ (xs.map (fun v => v.application Δ ds τ vs))

def JoinAt (E : Environment) (σ : Ty) : Prop := ∀ Γ xs,
  WellFormed E.types E.ports Γ → (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).join Γ xs ∈ (descriptor E σ).carriers Γ ∧
  (∀ x, x ∈ xs → (descriptor E σ).le Γ x ((descriptor E σ).join Γ xs) = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ xs → (descriptor E σ).le Γ x b = true) →
    (descriptor E σ).le Γ ((descriptor E σ).join Γ xs) b = true)

def MeetAt (E : Environment) (σ : Ty) : Prop := ∀ Γ xs,
  WellFormed E.types E.ports Γ → (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).meet Γ xs ∈ (descriptor E σ).carriers Γ ∧
  (∀ x, x ∈ xs → (descriptor E σ).le Γ ((descriptor E σ).meet Γ xs) x = true) ∧
  (∀ b, b ∈ (descriptor E σ).carriers Γ →
    (∀ x, x ∈ xs → (descriptor E σ).le Γ b x = true) →
    (descriptor E σ).le Γ b ((descriptor E σ).meet Γ xs) = true)

def RestrictionAt (E : Environment) (σ : Ty) : Prop := ∀ Γ Θ xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  (∀ x, x ∈ xs → x ∈ (descriptor E σ).carriers Γ) →
  (descriptor E σ).restrict Γ Θ ((descriptor E σ).join Γ xs) =
    (descriptor E σ).join Θ (xs.map ((descriptor E σ).restrict Γ Θ)) ∧
  (descriptor E σ).restrict Γ Θ ((descriptor E σ).meet Γ xs) =
    (descriptor E σ).meet Θ (xs.map ((descriptor E σ).restrict Γ Θ))

def LatticeAt (E : Environment) (σ : Ty) : Prop := JoinAt E σ ∧ MeetAt E σ ∧ RestrictionAt E σ

def LowerLattice (E : Environment) (σ : Ty) : Prop :=
  ∀ ρ, typeSize ρ < typeSize σ → LatticeAt E ρ

def AggregateValid : Prop := ∀ E σ Γ meet xs,
  WellFormed E.types E.ports Γ → LowerLattice E σ →
  (∀ v, v ∈ xs → Valid E σ Γ v) → Valid E σ Γ (aggregate E meet xs)

def CombineEncoding : Prop := ∀ E σ Γ meet cs,
  WellFormed E.types E.ports Γ → LowerLattice E σ →
  (∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) →
  combine E σ (canonicalLower E σ) Γ meet cs =
    encode E σ Γ (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ)))

def AggregateOrder : Prop := ∀ E σ Γ xs,
  WellFormed E.types E.ports Γ → LowerLattice E σ →
  (∀ v, v ∈ xs → Valid E σ Γ v) →
  (∀ v, v ∈ xs → SemanticLE E σ Γ v (aggregate E false xs)) ∧
  (∀ v, v ∈ xs → SemanticLE E σ Γ (aggregate E true xs) v) ∧
  (∀ b, Valid E σ Γ b → (∀ v, v ∈ xs → SemanticLE E σ Γ v b) →
    SemanticLE E σ Γ (aggregate E false xs) b) ∧
  (∀ b, Valid E σ Γ b → (∀ v, v ∈ xs → SemanticLE E σ Γ b v) →
    SemanticLE E σ Γ b (aggregate E true xs))

/- Literal paired-list relation, with no truncation or permutation. -/
inductive Pointwise {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pointwise R [] []
  | cons {a : α} {b : β} {xs : List α} {ys : List β} :
      R a b → Pointwise R xs ys → Pointwise R (a::xs) (b::ys)

def AggregateCongruence : Prop := ∀ E σ Γ meet xs ys,
  Pointwise (ValueEq E σ Γ) xs ys →
  ValueEq E σ Γ (aggregate E meet xs) (aggregate E meet ys)

def AggregateRestriction : Prop := ∀ E σ Γ Θ meet (cs : List Code),
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  (∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) →
  ValueEq E σ Θ (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ)))
    (aggregate E meet ((cs.map ((descriptor E σ).restrict Γ Θ)).map (HereditaryDomainSemantics.decode E σ Θ)))

def LatticeStep : Prop := ∀ E σ, LowerLattice E σ → LatticeAt E σ

end LogicLineages.PersistentMarking.HereditaryLatticeTargets
