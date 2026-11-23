module

public import LogicLineages.NativeModule.PersistentMarking.SpineTypingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.SpineShiftProof
open Spine

theorem annotationExact (Γ : BoundContext) (q : Expr) (σ : Ty) (h : Typed Γ q σ) :
    q.type = σ := by
  cases h with
  | free => rfl
  | bound _ => rfl
  | lam hb => simp only [Expr.type, annotationExact _ _ _ hb]
  | head _ => rfl
  | marked _ _ => rfl
termination_by sizeOf q

theorem compatiblePush (amount cutoff : Nat) (Γ Δ : BoundContext)
    (hc : ShiftCompatible amount cutoff Γ Δ) (δ : Ty) :
    ShiftCompatible amount (cutoff+1) (Γ.push δ) (Δ.push δ) := by
  intro i σ hi
  cases i with
  | zero => simpa [BoundContext.push] using hi
  | succ i =>
    have hh := hc i σ hi
    by_cases hlt : i < cutoff
    · simpa [BoundContext.push, hlt, Nat.succ_lt_succ_iff] using hh
    · simpa [BoundContext.push, hlt, Nat.succ_lt_succ_iff, Nat.succ_add] using hh

theorem compatibleOne (Γ : BoundContext) (δ : Ty) :
    ShiftCompatible 1 0 Γ (Γ.push δ) := by
  intro i σ hi
  simpa [BoundContext.push] using hi

mutual
 theorem shiftPreserves (Γ Δ : BoundContext) (q : Expr) (σ : Ty) (amount cutoff : Nat)
    (h : Typed Γ q σ) (hc : ShiftCompatible amount cutoff Γ Δ) :
    Typed Δ (shift amount cutoff q) σ := by
  cases h with
  | free => exact .free
  | bound hi => exact .bound (hc _ _ hi)
  | lam hb => exact .lam (shiftPreserves _ _ _ _ _ _ hb (compatiblePush _ _ _ _ hc _))
  | head hb => exact .head (shiftBasePreserves _ _ _ _ _ _ hb hc)
  | marked hb he =>
    exact .marked (shiftBasePreserves _ _ _ _ _ _ hb hc)
      (shiftExtrasPreserves _ _ _ _ _ he hc)
 termination_by sizeOf q
 theorem shiftBasePreserves (Γ Δ : BoundContext) (qs : Args) (types : List Ty)
    (amount cutoff : Nat) (h : BaseTyped Γ qs types)
    (hc : ShiftCompatible amount cutoff Γ Δ) :
    BaseTyped Δ (shiftArgs amount cutoff qs) types := by
  cases h with
  | nil => exact .nil
  | cons hx hxs =>
    exact .cons (shiftPreserves _ _ _ _ _ _ hx hc)
      (shiftBasePreserves _ _ _ _ _ _ hxs hc)
 termination_by sizeOf qs
 theorem shiftExtrasPreserves (Γ Δ : BoundContext) (qs : Args)
    (amount cutoff : Nat) (h : ExtrasTyped Γ qs)
    (hc : ShiftCompatible amount cutoff Γ Δ) :
    ExtrasTyped Δ (shiftArgs amount cutoff qs) := by
  cases h with
  | nil => exact .nil
  | cons hx hxs =>
    exact .cons (shiftPreserves _ _ _ _ _ _ hx hc)
      (shiftExtrasPreserves _ _ _ _ _ hxs hc)
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.SpineShiftProof
