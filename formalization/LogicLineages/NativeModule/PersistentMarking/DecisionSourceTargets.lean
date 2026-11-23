module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceUniverse

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceTargets
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse

def InitialUniverse : Prop := ∀ s t σ τ,
  Typed EmptyContext s σ → Typed EmptyContext t τ → Ordinary s → Ordinary t →
  let I := inventory s t
  Closed I.types ∧ Universe I.types I.names I.sourceHeads (List.replicate I.ports none) s

def RootType : Prop := ∀ K V H Γ q, Universe K V H Γ q → q.type ∈ K

def SourceOccurrence : Prop := ∀ K V H Γ stack q locals r,
  Universe K V H Γ q → Occurs stack q locals r → Universe K V H Γ r

def SourceAt : Prop := ∀ K V H Γ qs i q,
  ArgsUniverse K V H Γ qs → At qs i q → Universe K V H Γ q

def SourceMark : Prop := ∀ K V H Γ q r,
  Universe K V H Γ q → mark q = some r → Universe K V H Γ r

def SourceRetype : Prop := ∀ K V H Γ f σ τ bs es,
  Closed K → Universe K V H Γ (.marked f τ bs es) → σ ∈ K →
  Universe K V H Γ (.marked f σ bs es)

def SourceBoundSubstitution : Prop := ∀ K V H Γ types vs q τ,
  Typed (BoundContext.prefix types EmptyContext) q τ → BaseTyped EmptyContext vs types →
  Universe K V H Γ q → ArgsUniverse K V H Γ vs →
  Universe K V H Γ (substitute vs 0 q)

def SourceFullCall : Prop := ∀ K V H Γ q σ args τ r,
  Closed K → Typed EmptyContext q σ → CallTyped EmptyContext σ args τ →
  Universe K V H Γ q → ArgsUniverse K V H Γ args → apply q args = some r →
  Universe K V H Γ r

def SourceOwnerTuple : Prop := ∀ K V H Γ f τ bs es domains q i,
  Closed K → Universe K V H Γ (.marked f τ bs es) →
  (At bs i q ∨ At es i q) → Typed EmptyContext q (ArrowPrefix domains τ) →
  ArgsUniverse K V H Γ (ownerCopies f bs es domains)

def UniverseWeakening : Prop := ∀ K V H Γ Δ q,
  Extends Γ Δ → Universe K V H Γ q → Universe K V H Δ q

def ObservedTypes : Prop := ∀ S s t σ τ Γ υ r,
  PaperTerm S s σ → PaperTerm S t τ → Ordinary s → Ordinary t →
  WellFormed (inventory s t).types (inventory s t).ports Γ →
  r ∈ observations (inventory s t).names (inventory s t).ports Γ t υ →
  ∀ ρ, ρ ∈ auxiliarySupport r → ρ ∈ (inventory s t).types
end LogicLineages.PersistentMarking.DecisionSourceTargets
