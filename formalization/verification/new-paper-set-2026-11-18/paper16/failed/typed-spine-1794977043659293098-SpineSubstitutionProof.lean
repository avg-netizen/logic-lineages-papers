import LogicLineages.PersistentMarking.SpineShiftProof
import LogicLineages.PersistentMarking.InsertionProof
namespace LogicLineages.PersistentMarking.SpineSubstitutionProof
open Spine

theorem compatiblePush (values : Args) (depth : Nat) (Γ Δ : BoundContext)
    (hc : SubCompatible values depth Γ Δ) (δ : Ty) :
    SubCompatible values (depth+1) (Γ.push δ) (Δ.push δ) := by
  intro i σ hi
  cases i with
  | zero =>
    have hσ : δ = σ := Option.some.inj hi
    subst σ
    simpa [substitute, BoundContext.push] using
      (Typed.bound (Γ := Δ.push δ) (i := 0) (σ := δ) rfl)
  | succ i =>
    have ht := hc i σ hi
    have hh := SpineShiftProof.shiftPreserves Δ (Δ.push δ) _ σ 1 0 ht
      (SpineShiftProof.compatibleOne Δ δ)
    rw [InsertionProof.boundUnderBinder] 
    exact hh

mutual
 theorem preserves (Γ Δ : BoundContext) (q : Expr) (σ : Ty) (values : Args) (depth : Nat)
    (h : Typed Γ q σ) (hc : SubCompatible values depth Γ Δ) :
    Typed Δ (substitute values depth q) σ := by
  cases h with
  | free => exact .free
  | bound hi => exact hc _ _ hi
  | lam hb => exact .lam (preserves _ _ _ _ _ _ hb (compatiblePush _ _ _ _ hc _))
  | head hb => exact .head (basePreserves _ _ _ _ _ _ hb hc)
  | marked hb he =>
    exact .marked (basePreserves _ _ _ _ _ _ hb hc) (extrasPreserves _ _ _ _ _ he hc)
 termination_by sizeOf q
 theorem basePreserves (Γ Δ : BoundContext) (qs : Args) (types : List Ty)
    (values : Args) (depth : Nat) (h : BaseTyped Γ qs types)
    (hc : SubCompatible values depth Γ Δ) :
    BaseTyped Δ (substituteArgs values depth qs) types := by
  cases h with
  | nil => exact .nil
  | cons hx hxs => exact .cons (preserves _ _ _ _ _ _ hx hc) (basePreserves _ _ _ _ _ _ hxs hc)
 termination_by sizeOf qs
 theorem extrasPreserves (Γ Δ : BoundContext) (qs : Args)
    (values : Args) (depth : Nat) (h : ExtrasTyped Γ qs)
    (hc : SubCompatible values depth Γ Δ) :
    ExtrasTyped Δ (substituteArgs values depth qs) := by
  cases h with
  | nil => exact .nil
  | cons hx hxs => exact .cons (preserves _ _ _ _ _ _ hx hc) (extrasPreserves _ _ _ _ _ hxs hc)
 termination_by sizeOf qs
end

theorem consSuccessor (v : Expr) (rest : Args) (σ : Ty) (i : Nat) :
    substitute (.cons v rest) 0 (.bound σ (i+1)) =
      substitute rest 0 (.bound σ i) := by
  simp only [substitute, Nat.not_lt_zero, if_false, Nat.sub_zero, Args.get]
  cases hg : rest.get i with
  | some x => rfl
  | none => simp [Args.length, Nat.add_comm, Nat.add_sub_add_right]

theorem finiteCompatible (Γ : BoundContext) (values : Args) (types : List Ty)
    (hv : BaseTyped Γ values types) :
    SubCompatible values 0 (BoundContext.«prefix» types Γ) Γ := by
  intro i σ hi
  cases values with
  | nil =>
    cases hv
    rw [SubstitutionProof.emptySubstitution]
    exact .bound hi
  | cons x xs =>
    cases hv with
    | cons hx hxs =>
      cases i with
      | zero =>
        simp only [BoundContext.«prefix», BoundContext.push, Option.some.injEq] at hi
        subst σ
        simpa [substitute, Args.get, SubstitutionProof.shiftZero] using hx
      | succ i =>
        rw [consSuccessor]
        exact finiteCompatible _ _ _ hxs i σ hi
termination_by sizeOf values

theorem parallelPreserves : SpineTypingTargets.ParallelPreserves := by
  intro Γ types values q σ hv hq
  exact preserves _ _ _ _ _ _ hq (finiteCompatible _ _ _ hv)
theorem parallelBasePreserves : SpineTypingTargets.ParallelBasePreserves := by
  intro Γ types values qs τs hv hq
  exact basePreserves _ _ _ _ _ _ hq (finiteCompatible _ _ _ hv)
theorem parallelExtrasPreserves : SpineTypingTargets.ParallelExtrasPreserves := by
  intro Γ types values qs hv hq
  exact extrasPreserves _ _ _ _ _ hq (finiteCompatible _ _ _ hv)
end LogicLineages.PersistentMarking.SpineSubstitutionProof
