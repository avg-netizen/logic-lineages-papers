import LogicLineages.PersistentMarking.HereditaryDomainTargets
namespace LogicLineages.PersistentMarking.HereditaryOrderTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

def SemanticLE (E : Environment) (σ : Ty) (Γ : Context) (a b : Value) : Prop :=
  ∀ Δ, WellFormed E.types E.ports Δ → Extends Γ Δ →
  (a.available Δ = true → b.available Δ = true) ∧
  (∀ t, t ∈ DecisionObservations.observations E.names E.ports Δ E.target σ →
    (a.weak Δ t = true → b.weak Δ t = true) ∧ (a.strict Δ t = true → b.strict Δ t = true)) ∧
  (∀ ds τ, (ds,τ) ∈ fullPrefixes σ → ∀ vs, TupleValues E Δ ds vs →
    (descriptor E τ).le Δ (a.application Δ ds τ vs) (b.application Δ ds τ vs) = true)

def CarrierOrder (E : Environment) (σ : Ty) : Prop := ∀ Γ,
  WellFormed E.types E.ports Γ →
  (∀ a, a ∈ (descriptor E σ).carriers Γ → (descriptor E σ).le Γ a a = true) ∧
  (∀ a b c, a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
    c ∈ (descriptor E σ).carriers Γ → (descriptor E σ).le Γ a b = true →
    (descriptor E σ).le Γ b c = true → (descriptor E σ).le Γ a c = true) ∧
  (∀ a b, a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
    (descriptor E σ).le Γ a b = true → (descriptor E σ).le Γ b a = true → a=b)

def LowerOrder (E : Environment) (σ : Ty) : Prop :=
  ∀ ρ, typeSize ρ < typeSize σ → CarrierOrder E ρ

def EncodingCongruence : Prop := ∀ E σ Γ a b,
  ValueEq E σ Γ a b → encode E σ Γ a = encode E σ Γ b

def CodeInjective : Prop := ∀ E σ Γ a b,
  a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
  ValueEq E σ Γ (HereditaryDomainSemantics.decode E σ Γ a) (HereditaryDomainSemantics.decode E σ Γ b) → a=b

def CodeOrderExact : Prop := ∀ E σ Γ a b,
  WellFormed E.types E.ports Γ → a ∈ (descriptor E σ).carriers Γ → b ∈ (descriptor E σ).carriers Γ →
  ((descriptor E σ).le Γ a b = true ↔
    SemanticLE E σ Γ (HereditaryDomainSemantics.decode E σ Γ a) (HereditaryDomainSemantics.decode E σ Γ b))

def SemanticOrderLaws : Prop := ∀ E σ Γ,
  WellFormed E.types E.ports Γ → LowerOrder E σ →
  (∀ a, Valid E σ Γ a → SemanticLE E σ Γ a a) ∧
  (∀ a b c, Valid E σ Γ a → Valid E σ Γ b → Valid E σ Γ c →
    SemanticLE E σ Γ a b → SemanticLE E σ Γ b c → SemanticLE E σ Γ a c) ∧
  (∀ a b, Valid E σ Γ a → Valid E σ Γ b →
    SemanticLE E σ Γ a b → SemanticLE E σ Γ b a → ValueEq E σ Γ a b)

def OrderStep : Prop := ∀ E σ, LowerOrder E σ → CarrierOrder E σ

end LogicLineages.PersistentMarking.HereditaryOrderTargets
