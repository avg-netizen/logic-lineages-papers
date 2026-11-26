import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFiniteBinderProof
open NumberedWindowTypingBits NumberedWindowTypingBitsTargets

theorem push (Γ : List Ty) (σ : Ty) :
    (binderLookup Γ).push σ = binderLookup (σ :: Γ) := by
  funext i
  cases i <;> rfl

theorem extend (Γ Δ : List Ty) :
    Spine.BoundContext.«prefix» Δ (binderLookup Γ) = binderLookup (Δ ++ Γ) := by
  induction Δ with
  | nil => rfl
  | cons σ Δ ih =>
    change (Spine.BoundContext.«prefix» Δ (binderLookup Γ)).push σ =
      binderLookup (σ :: (Δ ++ Γ))
    rw [ih,push]

theorem lookup (Γ : List Ty) :
    binderLookup Γ = Spine.BoundContext.«prefix» Γ Spine.EmptyContext := by
  have h := (extend [] Γ).symm
  simpa only [List.append_nil] using h

theorem all : FiniteBinderLookup := ⟨lookup,push,extend⟩

end LogicLineages.PersistentMarking.NumberedWindowFiniteBinderProof
