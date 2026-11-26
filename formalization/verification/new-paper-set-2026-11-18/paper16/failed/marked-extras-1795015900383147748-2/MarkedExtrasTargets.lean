import LogicLineages.PersistentMarking.MarkedExtras
namespace LogicLineages.PersistentMarking.MarkedExtrasTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

def UniverseExact : Prop := ∀ E Γ σ c,
  (σ,c) ∈ «universe» E Γ ↔ σ ∈ E.types ∧ c ∈ (descriptor E σ).carriers Γ

def UniverseDistinct : Prop := ∀ E Γ, («universe» E Γ).Pairwise (· ≠ ·)

def TaggedOrder : Prop := ∀ E Γ, WellFormed E.types E.ports Γ →
  (∀ a, a ∈ «universe» E Γ → le E Γ a a = true) ∧
  (∀ a b c, a ∈ «universe» E Γ → b ∈ «universe» E Γ → c ∈ «universe» E Γ →
    le E Γ a b = true → le E Γ b c = true → le E Γ a c = true) ∧
  (∀ a b, a ∈ «universe» E Γ → b ∈ «universe» E Γ →
    le E Γ a b = true → le E Γ b a = true → a=b)

def DownExact : Prop := ∀ E Γ xs b,
  b ∈ down E Γ xs ↔ b ∈ «universe» E Γ ∧ ∃ a, a ∈ xs ∧ le E Γ b a = true

def DownIsExtra : Prop := ∀ E Γ xs, WellFormed E.types E.ports Γ →
  (∀ a, a ∈ xs → a ∈ «universe» E Γ) → Extra E Γ (down E Γ xs)

def DownIdentity : Prop := ∀ E Γ xs, WellFormed E.types E.ports Γ → Extra E Γ xs → down E Γ xs = xs

def Enumeration : Prop := ∀ E Γ xs, xs ∈ extras E Γ ↔ Extra E Γ xs

def RestrictionMonotone : Prop := ∀ E Γ Θ,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ →
  (∀ a, a ∈ «universe» E Γ → restricted E Γ Θ a ∈ «universe» E Θ) ∧
  (∀ a b, a ∈ «universe» E Γ → b ∈ «universe» E Γ → le E Γ a b = true →
    le E Θ (restricted E Γ Θ a) (restricted E Γ Θ b) = true)

def Weakening : Prop := ∀ E Γ Θ xs,
  WellFormed E.types E.ports Γ → WellFormed E.types E.ports Θ → Extends Γ Θ → Extra E Γ xs →
  Extra E Θ (weaken E Γ Θ xs)

def WeakeningAlgebra : Prop := ∀ E,
  (∀ Γ xs, WellFormed E.types E.ports Γ → Extra E Γ xs → weaken E Γ Γ xs = xs) ∧
  (∀ Γ Δ Θ xs, WellFormed E.types E.ports Γ → WellFormed E.types E.ports Δ →
    WellFormed E.types E.ports Θ → Extends Γ Δ → Extends Δ Θ → Extra E Γ xs →
    weaken E Δ Θ (weaken E Γ Δ xs) = weaken E Γ Θ xs)
end LogicLineages.PersistentMarking.MarkedExtrasTargets
