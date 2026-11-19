import LogicLineages.PersistentMarking.NumberedWindowLiteralEquality
import LogicLineages.PersistentMarking.NumberedWindowTypingBits

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowLiteralEquality NumberedWindowTypingBits

def LiteralTermEquality : Prop := ∀ Q R, termEq Q R = true ↔ Q = R

def LiteralArgsEquality : Prop := ∀ qs rs, argsEq qs rs = true ↔ qs = rs

def FiniteBinderLookup : Prop :=
  (∀ Γ, binderLookup Γ = Spine.BoundContext.«prefix» Γ Spine.EmptyContext) ∧
  (∀ Γ σ, (binderLookup Γ).push σ = binderLookup (σ::Γ)) ∧
  (∀ Γ Δ, Spine.BoundContext.«prefix» Δ (binderLookup Γ) = binderLookup (Δ ++ Γ))

def ExactTypedBit : Prop := ∀ C τ Q, typedBit C τ Q = true ↔ Typed C Q τ

def ExactBaseBit : Prop := ∀ C types qs, baseBit C types qs = true ↔ BaseTyped C qs types

def ExactExtrasBit : Prop := ∀ C qs, extrasBit C qs = true ↔ ExtrasTyped C qs

def ExactWindowBit : Prop :=
  ∀ S K C τ Q, windowBit S K C τ Q = true ↔ InWindow S K C τ Q

def ExactFiniteWindowBit : Prop :=
  ∀ S K Γ τ Q, finiteWindowBit S K Γ τ Q = true ↔
    InWindow S K (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) τ Q

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets
