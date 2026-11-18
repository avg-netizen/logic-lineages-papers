import LogicLineages.PersistentMarking.SpineTyping
namespace LogicLineages.PersistentMarking.SpineTypingTargets
open Spine

def AnnotationExact : Prop := ∀ Γ q σ, Typed Γ q σ → q.type = σ
def ShiftPreserves : Prop := ∀ Γ Δ q σ amount cutoff,
  Typed Γ q σ → ShiftCompatible amount cutoff Γ Δ → Typed Δ (shift amount cutoff q) σ

def ParallelPreserves : Prop := ∀ Γ types values q σ,
  BaseTyped Γ values types → Typed (BoundContext.prefix types Γ) q σ →
    Typed Γ (substitute values 0 q) σ

def ParallelBasePreserves : Prop := ∀ Γ types values qs τs,
  BaseTyped Γ values types → BaseTyped (BoundContext.prefix types Γ) qs τs →
    BaseTyped Γ (substituteArgs values 0 qs) τs

def ParallelExtrasPreserves : Prop := ∀ Γ types values qs,
  BaseTyped Γ values types → ExtrasTyped (BoundContext.prefix types Γ) qs →
    ExtrasTyped Γ (substituteArgs values 0 qs)

def ConsumeExact : Prop := ∀ Γ σ args τ, CallTyped Γ σ args τ → consumeTypes σ args = some τ

def CallPreserves : Prop := ∀ Γ q σ args τ r,
  Typed Γ q σ → CallTyped Γ σ args τ → apply q args = some r → Typed Γ r τ
end LogicLineages.PersistentMarking.SpineTypingTargets
