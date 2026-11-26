module

public import LogicLineages.NativeModule.PersistentMarking.SpineMarkingTargets
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.FreeTypingProof
open Spine

theorem prefixLookup (Γ : BoundContext) (types : List Ty) (i : Nat) :
    BoundContext.«prefix» types Γ (i+types.length) = Γ i := by
  induction types with
  | nil => rfl
  | cons σ types ih =>
    simpa only [BoundContext.«prefix», List.length_cons, Nat.add_succ, BoundContext.push] using ih

theorem prefixCompatible (Γ : BoundContext) (types : List Ty) :
    ShiftCompatible types.length 0 Γ (BoundContext.«prefix» types Γ) := by
  intro i σ hi
  simpa only [Nat.not_lt_zero, if_false, prefixLookup] using hi

mutual
 theorem preserves (Γ : BoundContext) (θ : FreeMap) (ht : FreeMapTyped Γ θ)
    (types : List Ty) (q : Expr) (σ : Ty)
    (h : Typed (BoundContext.«prefix» types Γ) q σ) :
    Typed (BoundContext.«prefix» types Γ) (freeSub θ types.length q) σ := by
  cases q with
  | free δ x =>
    cases h
    exact SpineShiftProof.shiftPreserves _ _ _ _ _ _ (ht _ x) (prefixCompatible Γ types)
  | bound δ i => exact h
  | lam δ body =>
    cases h with
    | lam hb => exact .lam (preserves Γ θ ht (δ::types) body _ hb)
  | head f base =>
    cases h with
    | head hb => exact .head (basePreserves Γ θ ht types base _ hb)
  | marked f τ base extras =>
    cases h with
    | marked hb he =>
      exact .marked (basePreserves Γ θ ht types base _ hb)
        (extrasPreserves Γ θ ht types extras he)
 termination_by sizeOf q
 theorem basePreserves (Γ : BoundContext) (θ : FreeMap) (ht : FreeMapTyped Γ θ)
    (types : List Ty) (qs : Args) (tys : List Ty)
    (h : BaseTyped (BoundContext.«prefix» types Γ) qs tys) :
    BaseTyped (BoundContext.«prefix» types Γ) (freeSubArgs θ types.length qs) tys := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (preserves Γ θ ht types q _ hq) (basePreserves Γ θ ht types qs _ hqs)
 termination_by sizeOf qs
 theorem extrasPreserves (Γ : BoundContext) (θ : FreeMap) (ht : FreeMapTyped Γ θ)
    (types : List Ty) (qs : Args)
    (h : ExtrasTyped (BoundContext.«prefix» types Γ) qs) :
    ExtrasTyped (BoundContext.«prefix» types Γ) (freeSubArgs θ types.length qs) := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (preserves Γ θ ht types q _ hq) (extrasPreserves Γ θ ht types qs hqs)
 termination_by sizeOf qs
end

theorem underBinders : SpineMarkingTargets.FreeSubTypedUnderBinders := preserves

theorem freeSubTyped : SpineMarkingTargets.FreeSubTyped := by
  intro Γ θ ht q σ h
  exact preserves Γ θ ht [] q σ h
end LogicLineages.PersistentMarking.FreeTypingProof
